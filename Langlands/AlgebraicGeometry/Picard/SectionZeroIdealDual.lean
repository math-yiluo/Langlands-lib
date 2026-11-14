import Langlands.AlgebraicGeometry.Picard.SectionZeroIdealUnits
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionClasses

/-! # The ideal of the zero locus of a regular section is the dual line bundle

For a regular global section `σ` of a line bundle `L`, evaluation at `σ` identifies the dual
`L^∨` with the ideal sheaf of the zero locus `D` of `σ`. Hence `D` is an effective Cartier
divisor and `O(D) ≅ L`. We also show that the zero locus of the canonical section of `O(D)` is
`D` for every effective Cartier divisor `D`. -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal

variable {X : Scheme.{u}}

section Coordinates

variable {M : X.Modules} {W V : X.Opens}
  (t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) (i : V ⟶ W)

/-- The coordinate functional of a trivialization, restricted to `V`. -/
abbrev dualGen : Γ(dual M, V) := (dual M).presheaf.map i.op (trivDualGen t)

/-- The coordinate of a section in a trivialization. -/
abbrev coord (m : Γ(M, V)) : Γ(X, V) := dualEval M V (dualGen t i) m

lemma coord_smul_trivGen (m : Γ(M, V)) : coord t i m • trivGen t i = m :=
  trivGen_expansion t i m

lemma coord_trivGen : coord t i (trivGen t i) = 1 := trivDualGen_eval t i

/-- The coordinate linear equivalence of a trivialization. -/
def coordEquiv : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun := coord t i
  invFun a := a • trivGen t i
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv m := coord_smul_trivGen t i m
  right_inv a := by
    change dualEval M V (dualGen t i) (a • trivGen t i) = a
    rw [map_smul, smul_eq_mul,
      show dualEval M V (dualGen t i) (trivGen t i) = 1 from coord_trivGen t i, mul_one]

/-- The coordinate of a dual section: its value on the generator. -/
def dualCoordEquiv : Γ(dual M, V) ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun φ := dualEval M V φ (trivGen t i)
  invFun a := a • dualGen t i
  map_add' φ ψ := by rw [map_add, LinearMap.add_apply]
  map_smul' r φ := by rw [map_smul, LinearMap.smul_apply]; rfl
  left_inv φ := (trivDual_expansion t i φ)
  right_inv a := by
    change dualEval M V (a • dualGen t i) (trivGen t i) = a
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
      show dualEval M V (dualGen t i) (trivGen t i) = 1 from coord_trivGen t i, mul_one]

include t i in
/-- In rank one, `λ(m) • n = λ(n) • m`. -/
lemma eval_smul_comm (φ : Γ(dual M, V)) (m n : Γ(M, V)) :
    dualEval M V φ m • n = dualEval M V φ n • m := by
  conv_lhs => rw [← coord_smul_trivGen t i m, ← coord_smul_trivGen t i n]
  conv_rhs => rw [← coord_smul_trivGen t i m, ← coord_smul_trivGen t i n]
  rw [map_smul, map_smul, smul_smul, smul_smul, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

/-- A dual section is determined by its value on the generator. -/
lemma dual_eq_smul (φ : Γ(dual M, V)) :
    φ = dualEval M V φ (trivGen t i) • dualGen t i :=
  (trivDual_expansion t i φ).symm

end Coordinates

/-- Opens that are affine and lie in an open over which the line bundle is trivial. -/
def FrameOpen (L : LineBundle X) (V : X.Opens) : Prop :=
  IsAffineOpen V ∧ ∃ W : X.Opens, V ≤ W ∧
    Nonempty (L.obj.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)

lemma frameOpen_basis (L : LineBundle X) :
    ∀ (y : X) (U : X.Opens), y ∈ U → ∃ V, FrameOpen L V ∧ y ∈ V ∧ V ≤ U := by
  intro y U hyU
  obtain ⟨W, hyW, ⟨t⟩⟩ := L.property y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ U ⊓ W from ⟨hyU, hyW⟩) (U ⊓ W).2
  exact ⟨V, ⟨hV, W, hVUW.trans inf_le_right, ⟨t⟩⟩, hyV, hVUW.trans inf_le_left⟩

section Dual

variable {L : LineBundle X} (σ : Γ(L.obj, ⊤))

lemma res_map {V V' : X.Opens} (h : V' ≤ V) :
    L.obj.presheaf.map (homOfLE h).op (res L σ V) = res L σ V' := by
  change L.obj.presheaf.map _ (L.obj.presheaf.map _ σ) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The kernel module of the zero ideal. -/
abbrev zeroKernel : X.Modules :=
  StructureKernelModule.kernelModule (zeroIdeal L σ).subschemeι

lemma eval_mem_ker {V : X.Opens} (hV : FrameOpen L V) (φ : Γ(dual L.obj, V)) :
    dualEval L.obj V φ (res L σ V) ∈ RingHom.ker ((zeroIdeal L σ).subschemeι.app V).hom := by
  obtain ⟨hVa, W, hVW, ⟨t⟩⟩ := hV
  have hk : RingHom.ker ((zeroIdeal L σ).subschemeι.app V).hom =
      (zeroIdeal L σ).ideal ⟨V, hVa⟩ :=
    Scheme.IdealSheafData.ker_subschemeι_app _ ⟨V, hVa⟩
  rw [hk]
  change _ ∈ (Submodule.span Γ(X, V) {res L σ V}).colon Set.univ
  rw [Submodule.mem_colon]
  intro m _
  rw [eval_smul_comm t (homOfLE hVW) φ (res L σ V) m]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- Evaluation at `σ`, from the dual to the kernel module, on a frame open. -/
def evalθ (V : X.Opens) (hV : FrameOpen L V) :
    Γ(dual L.obj, V) →ₗ[Γ(X, V)] Γ(zeroKernel σ, V) where
  toFun φ := ⟨dualEval L.obj V φ (res L σ V), eval_mem_ker σ hV φ⟩
  map_add' φ ψ := Subtype.ext (by
    change dualEval L.obj V (φ + ψ) (res L σ V) = _
    rw [map_add, LinearMap.add_apply]
    rfl)
  map_smul' r φ := Subtype.ext (by
    change dualEval L.obj V (r • φ) (res L σ V) = _
    rw [map_smul, LinearMap.smul_apply]
    rfl)

lemma evalθ_val (V : X.Opens) (hV : FrameOpen L V) (φ : Γ(dual L.obj, V)) :
    (evalθ σ V hV φ).1 = dualEval L.obj V φ (res L σ V) := rfl

lemma evalθ_compat (V V' : X.Opens) (hV : FrameOpen L V) (hV' : FrameOpen L V') (h : V' ≤ V)
    (φ : Γ(dual L.obj, V)) :
    (zeroKernel σ).presheaf.map (homOfLE h).op (evalθ σ V hV φ) =
      evalθ σ V' hV' ((dual L.obj).presheaf.map (homOfLE h).op φ) := by
  apply Subtype.ext
  change X.presheaf.map (homOfLE h).op (dualEval L.obj V φ (res L σ V)) =
    dualEval L.obj V' ((dual L.obj).presheaf.map (homOfLE h).op φ) (res L σ V')
  rw [← res_map σ h]
  exact (internalHomEval_restrict L.obj _ (homOfLE h) φ (res L σ V)).symm

/-- **Evaluation at `σ`** as a morphism `L^∨ ⟶ I_D`. -/
def evalHom : dual L.obj ⟶ zeroKernel σ :=
  (BasisHomGluing.exists_hom_of_basis (frameOpen_basis L) (evalθ σ) (evalθ_compat σ)).choose

lemma evalHom_app (V : X.Opens) (hV : FrameOpen L V) (φ : Γ(dual L.obj, V)) :
    (evalHom σ).app V φ = evalθ σ V hV φ :=
  (BasisHomGluing.exists_hom_of_basis (frameOpen_basis L) (evalθ σ) (evalθ_compat σ)).choose_spec
    V hV φ

variable {σ}

lemma bijective_evalθ (hσ : IsRegularSection L σ) (V : X.Opens) (hV : FrameOpen L V) :
    Function.Bijective (evalθ σ V hV) := by
  obtain ⟨hVa, W, hVW, ⟨t⟩⟩ := hV
  let i : V ⟶ W := homOfLE hVW
  have hσV : res L σ V = coord t i (res L σ V) • trivGen t i := (coord_smul_trivGen t i _).symm
  constructor
  · intro φ ψ h
    have h' := congrArg Subtype.val h
    rw [evalθ_val, evalθ_val] at h'
    rw [dual_eq_smul t i φ, dual_eq_smul t i ψ]
    congr 1
    rw [← sub_eq_zero]
    apply hσ V
    rw [hσV, smul_smul, sub_mul, sub_smul, mul_comm (dualEval L.obj V φ _),
      mul_comm (dualEval L.obj V ψ _), ← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul,
      ← hσV, h', sub_self]
  · rintro ⟨p, hp⟩
    have hp' : p ∈ (zeroIdeal L σ).ideal ⟨V, hVa⟩ := by
      have hk : RingHom.ker ((zeroIdeal L σ).subschemeι.app V).hom =
          (zeroIdeal L σ).ideal ⟨V, hVa⟩ :=
        Scheme.IdealSheafData.ker_subschemeι_app _ ⟨V, hVa⟩
      rw [← hk]
      exact hp
    rw [zeroIdeal_ideal_of_equiv L σ ⟨V, hVa⟩ (coordEquiv t i)] at hp'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hp'
    refine ⟨c • dualGen t i, Subtype.ext ?_⟩
    rw [evalθ_val, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact hc

/-- For a regular section, evaluation identifies `L^∨` with the ideal of its zero locus. -/
theorem isIso_evalHom (hσ : IsRegularSection L σ) : IsIso (evalHom σ) :=
  Modules.ProperFormalCoherentExistenceOfFLT.isIso_of_bijective_of_basis (frameOpen_basis L) (evalHom σ) fun V hV => by
    have : ((evalHom σ).app V : Γ(dual L.obj, V) → Γ(zeroKernel σ, V)) = evalθ σ V hV :=
      funext (evalHom_app σ V hV)
    rw [this]
    exact bijective_evalθ hσ V hV

/-- **The zero locus of a regular section is an effective Cartier divisor.** -/
theorem isEffectiveCartierIdeal_zeroIdeal (hσ : IsRegularSection L σ) :
    IsEffectiveCartierIdeal (zeroIdeal L σ) := by
  have := isIso_evalHom hσ
  exact (isLocallyFreeRankOne_dual L.property).of_iso (asIso (evalHom σ))

/-- **`O(D_σ) ≅ L`** for the zero locus `D_σ` of a regular section `σ` of `L`. -/
theorem nonempty_lineBundle_zeroIdeal_iso (hσ : IsRegularSection L σ) :
    Nonempty ((EffectiveCartierDivisor.lineBundle
      ⟨zeroIdeal L σ, isEffectiveCartierIdeal_zeroIdeal hσ⟩).obj ≅ L.obj) := by
  have := isIso_evalHom hσ
  rw [← LineBundle.classOf_eq_iff]
  change (EffectiveCartierDivisor.idealLineBundle
    ⟨zeroIdeal L σ, isEffectiveCartierIdeal_zeroIdeal hσ⟩).dual.classOf = L.classOf
  rw [PicardHilbertPiecesReduction.classOf_dual]
  have h : (EffectiveCartierDivisor.idealLineBundle
      ⟨zeroIdeal L σ, isEffectiveCartierIdeal_zeroIdeal hσ⟩).classOf = L.dual.classOf :=
    (LineBundle.classOf_eq_iff _ _).2 ⟨(asIso (evalHom σ)).symm⟩
  rw [h, PicardHilbertPiecesReduction.classOf_dual, neg_neg]

end Dual

section Canonical

variable (D : EffectiveCartierDivisor X)

/-- **The zero locus of the canonical section of `O(D)` is `D`.** -/
theorem zeroIdeal_canonicalSection : zeroIdeal D.lineBundle D.canonicalSection = D.ideal := by
  have hx : ∀ x : X, ∃ (V : X.affineOpens), x ∈ V.1 ∧ ∃ W : X.Opens, V.1 ≤ W ∧
      Nonempty (D.idealLineBundle.obj.restrict W.ι ≅
        SheafOfModules.unit W.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨V, hV, hxV, hVU⟩ := frameOpen_basis D.idealLineBundle x ⊤ trivial
    exact ⟨⟨V, hV.1⟩, hxV, hV.2⟩
  choose V hxV W hVW t using hx
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top V
    (top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) fun x => ?_
  let i : (V x).1 ⟶ W x := homOfLE (hVW x)
  let P := D.idealLineBundle.obj
  -- the generator of the ideal on `V x`
  let g : Γ(P, (V x).1) := trivGen (t x).some i
  let f : Γ(X, (V x).1) := g.1
  -- the ideal of `D` on `V x` is generated by `f`
  have hD : D.ideal.ideal (V x) = Ideal.span {f} := by
    ext a
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, Ideal.mem_span_singleton']
    constructor
    · intro ha
      let p : Γ(P, (V x).1) := ⟨a, ha⟩
      refine ⟨coord (t x).some i p, ?_⟩
      have := congrArg Subtype.val (coord_smul_trivGen (t x).some i p)
      exact this
    · rintro ⟨c, rfl⟩
      exact (c • g).2
  rw [hD, zeroIdeal_ideal_of_equiv D.lineBundle D.canonicalSection (V x)
    (dualCoordEquiv (t x).some i)]
  congr 1

end Canonical

end Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal
