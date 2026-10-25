import Langlands.AlgebraicGeometry.ModuleDualEvaluation
import Langlands.AlgebraicGeometry.ModuleDualLocalFree
import Langlands.AlgebraicGeometry.Picard.LineBundle

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard (IsLocallyFreeRankOne)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {W : X.Opens}

/-- A trivialization of the restriction of `M` to the open subscheme `W`, transported to the
category of module sheaves on the opens contained in `W`. -/
def overTrivialization
    (t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) :=
  (Scheme.Modules.overEquiv W).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv W).app M ≪≫ t ≪≫
      (Scheme.Modules.restrictUnitIso W.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv W).app (SheafOfModules.unit X.ringCatSheaf)).symm)

/-- The one-element local basis given by a trivialization. -/
def unitLocalBasis
    (t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    SheafOfModules.free (R := X.ringCatSheaf.over W) PUnit.{u + 1} ≅ M.over W :=
  coproductUniqueIso _ ≪≫ (overTrivialization t).symm

variable (t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)

/-- The local generator of `M` on an open `V ⊆ W`. -/
def trivGen {V : X.Opens} (i : V ⟶ W) : Γ(M, V) :=
  (localBasisSection (unitLocalBasis t) PUnit.unit).val (op (Over.mk i))

/-- The dual generator on `W`: the coordinate functional of the trivialization. -/
def trivDualGen : Γ(dual M, W) :=
  localBasisCoordinate (unitLocalBasis t) PUnit.unit

lemma trivGen_restrict {V V' : X.Opens} (i : V ⟶ W) (j : V' ⟶ V) :
    M.presheaf.map j.op (trivGen t i) = trivGen t (j ≫ i) :=
  PresheafOfModules.sections_property (localBasisSection (unitLocalBasis t) PUnit.unit)
    (Over.homMk j : Over.mk (j ≫ i) ⟶ Over.mk i).op

lemma trivDualGen_eval {V : X.Opens} (i : V ⟶ W) :
    dualEval M V ((dual M).presheaf.map i.op (trivDualGen t)) (trivGen t i) = 1 := by
  have h := localBasisCoordinate_basis (unitLocalBasis t) PUnit.unit PUnit.unit (Over.mk i)
  rw [ite_eq_left (rfl : PUnit.unit = PUnit.unit)] at h
  exact h

lemma trivGen_expansion {V : X.Opens} (i : V ⟶ W) (m : Γ(M, V)) :
    dualEval M V ((dual M).presheaf.map i.op (trivDualGen t)) m • trivGen t i = m := by
  have h := localBasis_expansion (unitLocalBasis t) (Over.mk i) m
  rw [Fintype.sum_unique] at h
  exact h

lemma trivDual_expansion {V : X.Opens} (i : V ⟶ W) (φ : Γ(dual M, V)) :
    dualEval M V φ (trivGen t i) • (dual M).presheaf.map i.op (trivDualGen t) = φ := by
  refine LocalHom.ext (M := M) (N := Langlands.SchemeModule.structureModule X) _ _
    (fun V' j => ?_)
  ext x
  have hx := trivGen_expansion t (j ≫ i) x
  have hnat := internalHomEval_restrict M (Langlands.SchemeModule.structureModule X) j φ
    (trivGen t i)
  rw [trivGen_restrict] at hnat
  change X.presheaf.map j.op (dualEval M V φ (trivGen t i)) •
      LocalHom.app (trivDualGen t) (j ≫ i) x = LocalHom.app φ j x
  conv_rhs => rw [← hx]
  rw [(LocalHom.app φ j).hom.map_smul]
  have h2 : (show Γ(X, V') from LocalHom.app φ j (trivGen t (j ≫ i))) =
      X.presheaf.map j.op (dualEval M V φ (trivGen t i)) := hnat
  change X.presheaf.map j.op (dualEval M V φ (trivGen t i)) *
      (show Γ(X, V') from LocalHom.app (trivDualGen t) (j ≫ i) x) =
    (show Γ(X, V') from LocalHom.app (trivDualGen t) (j ≫ i) x) *
      (show Γ(X, V') from LocalHom.app φ j (trivGen t (j ≫ i)))
  rw [h2, mul_comm]

/-- The sectionwise tensor evaluation `M(V) ⊗ M^∨(V) → O_X(V)`, valued in `Γ(X, V)`. -/
def tensorEvalSection (V : X.Opens) (x : (M.val ⊗ (dual M).val).obj (op V)) : Γ(X, V) :=
  ((tensorHomEquiv _ _ _ (dualTensorEval M)).app (op V)).hom x

lemma tensorEvalSection_tmul (V : X.Opens) (m : Γ(M, V)) (φ : Γ(dual M, V)) :
    tensorEvalSection V (m ⊗ₜ φ) = dualEval M V φ m :=
  tensorHomEquiv_dualTensorEval_app_tmul M V m φ

lemma tensorEvalSection_add (V : X.Opens) (x y : (M.val ⊗ (dual M).val).obj (op V)) :
    tensorEvalSection V (x + y) = tensorEvalSection V x + tensorEvalSection V y :=
  map_add ((tensorHomEquiv _ _ _ (dualTensorEval M)).app (op V)).hom x y

lemma gamma_smul_tmul (V : X.Opens) (a : Γ(X, V)) (m : Γ(M, V)) (φ : Γ(dual M, V)) :
    ((a • m) ⊗ₜ φ : (M.val ⊗ (dual M).val).obj (op V)) = m ⊗ₜ (a • φ) :=
  TensorProduct.smul_tmul _ _ _

lemma tensorEvalSection_expansion {V : X.Opens} (i : V ⟶ W)
    (x : (M.val ⊗ (dual M).val).obj (op V)) :
    ((tensorEvalSection V x • trivGen t i) ⊗ₜ (dual M).presheaf.map i.op (trivDualGen t) :
      (M.val ⊗ (dual M).val).obj (op V)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul m φ =>
    rw [tensorEvalSection_tmul]
    conv_rhs => rw [← trivDual_expansion t i φ]
    rw [← gamma_smul_tmul]
    congr 1
    conv_lhs => rw [← trivGen_expansion t i m]
    conv_rhs => rw [← trivGen_expansion t i m]
    rw [map_smul, smul_eq_mul, smul_smul, mul_comm]
  | add x y hx hy => rw [tensorEvalSection_add, add_smul, TensorProduct.add_tmul, hx, hy]

include t in
lemma bijective_tensorEvalSection {V : X.Opens} (i : V ⟶ W) :
    Function.Bijective (tensorEvalSection (M := M) V) := by
  constructor
  · intro x y hxy
    rw [← tensorEvalSection_expansion t i x, ← tensorEvalSection_expansion t i y, hxy]
  · intro s
    refine ⟨(s • trivGen t i) ⊗ₜ (dual M).presheaf.map i.op (trivDualGen t), ?_⟩
    rw [tensorEvalSection_tmul, map_smul, trivDualGen_eval, smul_eq_mul, mul_one]

/-- Near any point of an open `U`, a locally free module of rank one has a smaller open on
which the sectionwise tensor evaluation is bijective. -/
lemma exists_bijective_tensorEvalSection (hM : IsLocallyFreeRankOne M) {U : X.Opens} {x : X}
    (hx : x ∈ U) : ∃ (V : X.Opens) (_ : V ⟶ U), x ∈ V ∧
      Function.Bijective (tensorEvalSection (M := M) V) := by
  obtain ⟨W', hxW', ⟨t'⟩⟩ := hM x
  exact ⟨U ⊓ W', homOfLE inf_le_left, ⟨hx, hxW'⟩,
    bijective_tensorEvalSection t' (homOfLE inf_le_right)⟩

/-- For a locally free module of rank one, the evaluation `M ⊗ M^∨ → O_X` is an isomorphism. -/
theorem isIso_dualTensorEval (hM : IsLocallyFreeRankOne M) : IsIso (dualTensorEval M) := by
  let f₁ := (PresheafOfModules.toPresheaf _).map (tensorSheafifyUnit M (dual M))
  let f₂ := (PresheafOfModules.toPresheaf _).map (dualTensorEval M).val
  let f₃ := (PresheafOfModules.toPresheaf _).map (tensorHomEquiv _ _ _ (dualTensorEval M))
  have fac : f₁ ≫ f₂ = f₃ := by
    simp only [f₁, f₂, f₃]
    rw [← Functor.map_comp, ← tensorHomEquiv_eq_tensorSheafifyUnit_comp]
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f₁ :=
    (inferInstance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (M.val ⊗ (dual M).val).presheaf))
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f₃ := by
    constructor
    intro U s
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, j, hxV, hbij⟩ := exists_bijective_tensorEvalSection hM hx
    refine ⟨V, j, ?_, hxV⟩
    rw [Presheaf.imageSieve_apply]
    obtain ⟨y, hy⟩ :=
      hbij.2 (((PresheafOfModules.toPresheaf _).obj (structureSheaf X).val).map j.op s)
    exact ⟨y, hy⟩
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f₃ := by
    constructor
    intro U a b h
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, j, hxV, hbij⟩ := exists_bijective_tensorEvalSection hM hx
    refine ⟨V, j, ?_, hxV⟩
    rw [Presheaf.equalizerSieve_apply]
    apply hbij.1
    exact (NatTrans.naturality_apply f₃ j.op a).trans
      ((congrArg _ h).trans (NatTrans.naturality_apply f₃ j.op b).symm)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f₂ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f₂ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ f₃ fac
  have : IsIso ((SheafOfModules.toSheaf _).map (dualTensorEval M)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨inferInstanceAs (Presheaf.IsLocallyInjective _ f₂),
        inferInstanceAs (Presheaf.IsLocallySurjective _ f₂)⟩
  exact isIso_of_reflects_iso (C := SheafOfModules X.ringCatSheaf) (dualTensorEval M)
    (SheafOfModules.toSheaf X.ringCatSheaf)

/-- A trivialization over the opens contained in `W`, transported back to the restriction of
`N` to the open subscheme `W`. -/
def restrictTrivialization {N : X.Modules}
    (s : N.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    N.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv W).app N).symm ≪≫ (Scheme.Modules.overEquiv W).functor.mapIso s ≪≫
    (Scheme.Modules.overFunctorEquiv W).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso W.ι

/-- The dual of a locally free module of rank one is locally free of rank one. -/
theorem isLocallyFreeRankOne_dual (hM : IsLocallyFreeRankOne M) :
    IsLocallyFreeRankOne (dual M) := by
  intro x
  obtain ⟨W', hx, ⟨t'⟩⟩ := hM x
  exact ⟨W', hx, ⟨restrictTrivialization
    ((dualLocalFreeIso (unitLocalBasis t')).symm ≪≫ coproductUniqueIso _)⟩⟩

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- Every line bundle has a tensor inverse, namely its dual. -/
theorem LineBundle.exists_tensorObj_iso_structureSheaf {X : AlgebraicGeometry.Scheme.{u}}
    (L : LineBundle X) :
    ∃ M : LineBundle X,
      Nonempty (Langlands.Scheme.Modules.tensorObj L.obj M.obj ≅ structureSheaf X) := by
  have := isIso_dualTensorEval L.property
  exact ⟨⟨dual L.obj, isLocallyFreeRankOne_dual L.property⟩, ⟨asIso (dualTensorEval L.obj)⟩⟩

end Langlands.AlgebraicGeometry.Picard
