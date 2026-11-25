/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-!
# Affine presentations of a finite-type projective bundle

The local projective dimensions depend on the affine open. Neither the covering nor
these dimensions have a finite uniform bound.

## References

* Stacks Project, Morphisms, Tags 01WB and 087S, proofs
* Sheaves of Modules, Tags 01B5 and 01AM
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

private theorem finiteType_of_finite_generators {X : Scheme.{u}} (M : X.Modules)
    (σ : M.GeneratingSections) [σ.IsFiniteType] : M.IsFiniteType := by
  have : σ.localGeneratorsData.IsFiniteType := by
    refine { isFiniteType := ?_ }
    intro W
    change (σ.map _ _).IsFiniteType
    infer_instance
  exact SheafOfModules.IsFiniteType.mk (M := M) ⟨σ.localGeneratorsData, this⟩

private theorem pad_finite_generators {X : Scheme.{u}} (M : X.Modules)
    (σ : M.GeneratingSections) [Finite σ.I] :
    ∃ (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → M.sections),
      Epi (M.freeHomEquiv.symm s) := by
  classical
  let _ := Fintype.ofFinite σ.I
  let n := Fintype.card σ.I
  let e := Fintype.equivFin σ.I
  let f : σ.I → ULift.{u} (Fin (n + 1)) := fun i ↦ ⟨(e i).castSucc⟩
  let s : ULift.{u} (Fin (n + 1)) → M.sections := fun i ↦
    if h : i.down.val < n then σ.s (e.symm ⟨i.down.val, h⟩) else M.unitHomEquiv 0
  have hs (i : σ.I) : s (f i) = σ.s i := by
    simp [s, f, n]
  have heq : SheafOfModules.freeMap f ≫ M.freeHomEquiv.symm s = σ.π := by
    apply M.freeHomEquiv.injective
    funext i
    rw [SheafOfModules.freeHomEquiv_comp_apply, SheafOfModules.freeHomEquiv_freeMap]
    simpa only [Function.comp_apply,
      SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection,
      Equiv.apply_symm_apply] using hs i
  refine ⟨n, s, ?_⟩
  exact epi_of_epi_fac heq

private theorem finite_generators_affine_neighborhood (S : Scheme.{u}) (E : S.Modules)
    [E.IsFiniteType] (x : S) :
    ∃ (U : S.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ σ : (E.restrict U.ι).GeneratingSections, σ.IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData E
  have hcover : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset hxi
  let j : U ⟶ q.X i := homOfLE hUi
  let T := SheafOfModules.overMap S.ringCatSheaf j
  have : PreservesColimitsOfSize.{u, u} T := inferInstance
  let σ := ((q.generators i).map T
    (SheafOfModules.overMapUnitIso (R := S.ringCatSheaf) j).symm).ofEpi
      ((SheafOfModules.overFunctorMap S.ringCatSheaf j).app E).hom
  have : σ.IsFiniteType := ⟨(hq.isFiniteType i).finite⟩
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv U).functor :=
    (Scheme.Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  let τ := (σ.map (Scheme.Modules.overEquiv U).functor
    (Scheme.Modules.overEquivFunctorObjUnitIso U)).ofEpi
      ((Scheme.Modules.overFunctorEquiv U).app E).hom
  exact ⟨U, hxU, hU, τ, ⟨inferInstanceAs (Finite σ.I)⟩⟩

private theorem affine_surjective_of_epi {X : Scheme.{u}} {F E : X.Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent] (f : F ⟶ E) [Epi f]
    {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective (f.val.app (op U)) := by
  have h := (Scheme.Modules.quasiCoherent_cokernel_image f).2.2.2.2.2.2.2.2 ⟨U, hU⟩
  have hz : cokernel.π f = 0 := zero_of_epi_comp f (cokernel.condition f)
  have hz' : ((cokernel.π f).val.app (op U)).hom = 0 := by
    ext x
    change (cokernel.π f).app U x = 0
    rw [hz, Scheme.Modules.Hom.zero_app]
    rfl
  apply LinearMap.range_eq_top.mp
  simpa only [hz', LinearMap.ker_zero] using h.2.2.1.symm

private theorem finite_generators_span {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections)
    [Epi (E.freeHomEquiv.symm s)] (U : X.affineOpens) :
    Submodule.span (M := E.val.obj (op U.1)) Γ(X, U.1) (Set.range fun i : Fin (n + 1) ↦
      ((s (ULift.up i)).val (op U.1) : E.val.obj (op U.1))) = ⊤ := by
  classical
  let f := E.freeHomEquiv.symm s
  have : (SheafOfModules.free (R := X.ringCatSheaf)
      (ULift.{u} (Fin (n + 1)))).IsQuasicoherent := SheafOfModules.isQuasicoherent_free.{u, u, u} _
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := affine_surjective_of_epi f U.2 x
  have hy : (∑ i : ULift.{u} (Fin (n + 1)),
      (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U.1)
        ((Scheme.Modules.freeπ i).val.app (op U.1) y)) = y := by
    change (∑ i : ULift.{u} (Fin (n + 1)),
      (Scheme.Modules.Hom.app (Scheme.Modules.freeπ i ≫ SheafOfModules.ιFree i) U.1) y) = y
    rw [← Scheme.Modules.Hom.sum_app_apply, Scheme.Modules.sum_freeπ_ιFree]
    rfl
  have hs (i : ULift.{u} (Fin (n + 1))) :
      f.val.app (op U.1)
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U.1) (1 : Γ(X, U.1))) =
      (s i).val (op U.1) := by
    have he := congrArg (fun t ↦ t.val (op U.1))
      (congrFun (E.freeHomEquiv.apply_symm_apply s) i)
    exact he
  rw [← hy, map_sum]
  apply Submodule.sum_mem
  intro i _
  let c : Γ(X, U.1) := (Scheme.Modules.freeπ i).val.app (op U.1) y
  have hc : (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (op U.1) c =
      c • (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app
        (op U.1) (1 : Γ(X, U.1)) := by
    rw [← map_smul]
    congr 1
    exact (mul_one c).symm
  rw [hc, map_smul, hs]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i.down, rfl⟩)

@[irreducible] private noncomputable def polynomialPresentation {X : Scheme.{u}} (E : X.Modules)
    (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections) (U : X.Opens) :
    MvPolynomial (Fin (n + 1)) Γ(X, U) →ₐ[Γ(X, U)]
      SymmetricAlgebraSheaf.sections E (op U) :=
  MvPolynomial.aeval (fun i ↦ SymmetricAlgebra.ι Γ(X, U) _ ((s (ULift.up i)).val (op U)))

private theorem polynomialPresentation_C {X : Scheme.{u}} (E : X.Modules)
    (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections) (U : X.Opens) (r : Γ(X, U)) :
    polynomialPresentation E n s U (MvPolynomial.C r) = algebraMap _ _ r := by
  unfold polynomialPresentation
  exact MvPolynomial.aeval_C _ r

private theorem polynomialPresentation_X {X : Scheme.{u}} (E : X.Modules)
    (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections) (U : X.Opens) (i : Fin (n + 1)) :
    polynomialPresentation E n s U (MvPolynomial.X i) =
      SymmetricAlgebra.ι Γ(X, U) (E.val.obj (op U)) ((s (ULift.up i)).val (op U)) := by
  unfold polynomialPresentation
  exact MvPolynomial.aeval_X _ i

private theorem polynomialPresentation_homogeneous {X : Scheme.{u}} (E : X.Modules)
    (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections) (U : X.Opens)
    (d : ℕ) (p : MvPolynomial (Fin (n + 1)) Γ(X, U))
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, U) d) :
    polynomialPresentation E n s U p ∈
      (SymmetricAlgebra.ι Γ(X, U) (E.val.obj (op U))).range ^ d := by
  let q := polynomialPresentation E n s U
  have h₁ : (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, U) 1).map
      q.toLinearMap ≤ (SymmetricAlgebra.ι Γ(X, U) (E.val.obj (op U))).range := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨(s (ULift.up i)).val (op U), (polynomialPresentation_X E n s U i).symm⟩
  have hd := pow_le_pow_left' h₁ d
  rw [← Submodule.map_pow, MvPolynomial.homogeneousSubmodule_one_pow] at hd
  exact hd (Submodule.mem_map_of_mem hp)

private theorem polynomialPresentation_surjective {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections)
    [Epi (E.freeHomEquiv.symm s)] (U : X.affineOpens) :
    Function.Surjective (polynomialPresentation E n s U.1) := by
  let q := polynomialPresentation E n s U.1
  have hι (x : E.val.obj (op U.1)) :
      ∃ p, q p = SymmetricAlgebra.ι Γ(X, U.1) _ x := by
    have hx : x ∈ Submodule.span (M := E.val.obj (op U.1)) Γ(X, U.1)
        (Set.range fun i : Fin (n + 1) ↦
          ((s (ULift.up i)).val (op U.1) : E.val.obj (op U.1))) := by
      rw [finite_generators_span E n s U]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨MvPolynomial.X i, polynomialPresentation_X E n s U.1 i⟩
    | zero => exact ⟨0, (map_zero q).trans (map_zero _).symm⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | smul r x hx ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨MvPolynomial.C r * a, ?_⟩
      rw [map_mul, show q (MvPolynomial.C r) = algebraMap _ _ r from
        polynomialPresentation_C E n s U.1 r, ha, map_smul, Algebra.smul_def]
  intro z
  induction z using SymmetricAlgebra.induction with
  | algebraMap r => exact ⟨MvPolynomial.C r, polynomialPresentation_C E n s U.1 r⟩
  | ι x => exact hι x
  | mul a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a * b, map_mul q _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add q _ _⟩

private theorem polynomialPresentation_restriction {X : Scheme.{u}} (E : X.Modules)
    (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections)
    {U V : X.affineOpens} (h : U ≤ V)
    (p : MvPolynomial (Fin (n + 1)) Γ(X, V.1)) :
    polynomialPresentation E n s U.1
        (MvPolynomial.map (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom p) =
      SymmetricAlgebraSheaf.restriction E (homOfLE (X := X.Opens) h).op
        (polynomialPresentation E n s V.1 p) := by
  let qU := polynomialPresentation E n s U.1
  let qV := polynomialPresentation E n s V.1
  let ρ := SymmetricAlgebraSheaf.restriction E (homOfLE (X := X.Opens) h).op
  have he : qU.toRingHom.comp
      (MvPolynomial.map (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom) =
      ρ.comp qV.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      change qU (MvPolynomial.C _) = ρ (qV (MvPolynomial.C r))
      rw [polynomialPresentation_C, polynomialPresentation_C]
      exact (SymmetricAlgebraSheaf.restriction_algebraMap E _ r).symm
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X]
      change qU (MvPolynomial.X i) = ρ (qV (MvPolynomial.X i))
      rw [polynomialPresentation_X, polynomialPresentation_X]
      rw [SymmetricAlgebraSheaf.restriction_ι]
      exact congrArg (SymmetricAlgebra.ι _ _)
        (PresheafOfModules.sections_property (s (ULift.up i))
          (homOfLE (X := X.Opens) h).op).symm
  exact RingHom.congr_fun he p

private theorem projectiveBundle_embedding_of_generators (X : Scheme.{u}) (E : X.Modules)
    [E.IsQuasicoherent] (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → E.sections)
    [Epi (E.freeHomEquiv.symm s)] :
    ∃ j : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ⟶
        ℙ(ULift.{u} (Fin (n + 1)); X),
      IsClosedImmersion j ∧
        j ≫ ℙ(ULift.{u} (Fin (n + 1)); X) ↘ X =
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom := by
  classical
  obtain ⟨θ, hθ, _⟩ :=
    RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace X n
  let A := (RelativeProjectiveSpace.algebra X n).affineData
  let B := SymmetricAlgebraSheaf.gradedAlgebraData E
  let e := RelativeProjectiveSpace.affinePolynomialEquiv X n
  have heC (U : X.affineOpens) (r : Γ(X, U.1)) :
      e U (MvPolynomial.C r) = algebraMap Γ(X, U.1) (A.obj U) r :=
    (RelativeProjectiveSpace.existsUnique_affinePolynomialEquiv X n U).exists.choose_spec.1 r
  let f : A ⟶ B :=
    { app U :=
        { toRingHom := (polynomialPresentation E n s U.1).toRingHom.comp (e U).symm.toRingHom
          map_mem := by
            intro d x hx
            have hx' : e U ((e U).symm x) ∈
                (RelativeProjectiveSpace.algebra X n).sectionGrade U d := by
              rw [RingEquiv.apply_symm_apply]
              exact hx
            exact polynomialPresentation_homogeneous E n s U.1 d _
              ((RelativeProjectiveSpace.affinePolynomial_homogeneous X n U d _).mp hx') }
      app_algebraMap U r := by
        change polynomialPresentation E n s U.1
          ((e U).symm (algebraMap Γ(X, U.1) (A.obj U) r)) = _
        rw [← heC U r, RingEquiv.symm_apply_apply]
        exact polynomialPresentation_C E n s U.1 r
      naturality {U V} h x := by
        obtain ⟨p, rfl⟩ := (e V).surjective x
        change polynomialPresentation E n s U.1
            ((e U).symm ((RelativeProjectiveSpace.algebra X n).restriction h (e V p))) =
          SymmetricAlgebraSheaf.restriction E (homOfLE (X := X.Opens) h).op
            (polynomialPresentation E n s V.1 ((e V).symm (e V p)))
        rw [hθ.2.2.2 V U h p, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
        exact polynomialPresentation_restriction E n s h p }
  have hf (U : X.affineOpens) : Function.Surjective (f.app U) :=
    (polynomialPresentation_surjective E n s U).comp (e U).symm.surjective
  let i := Scheme.GradedAlgebraData.relProjMap f
    (Scheme.GradedAlgebraData.irrelevantLE_of_surjective f hf)
  have : IsClosedImmersion i := Scheme.GradedAlgebraData.isClosedImmersion_relProjMap f hf
  refine ⟨i ≫ θ.hom, inferInstance, ?_⟩
  rw [Category.assoc, hθ.1]
  exact Scheme.GradedAlgebraData.relProjMap_relProjHom f _

/-- A finite-type quasi-coherent module admits an affine open covering with finite
nonempty generating families and closed embeddings of its restricted projective bundles
into projective spaces of the corresponding dimensions, over the affine base. -/
theorem exists_affine_projectiveBundle_presentations (S : Scheme.{u}) (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) :
    ∃ (I : Type u) (U : I → S.Opens) (n : I → ℕ),
      (⨆ a : I, U a) = ⊤ ∧
      ∀ a : I, IsAffineOpen (U a) ∧
        ∃ s : ULift.{u} (Fin (n a + 1)) → (E.restrict (U a).ι).sections,
          Epi ((E.restrict (U a).ι).freeHomEquiv.symm s) ∧
          ∃ hq : (E.restrict (U a).ι).IsQuasicoherent,
            (E.restrict (U a).ι).IsFiniteType ∧
            ∃ j : (@SymmetricAlgebraSheaf.gradedAlgebraData (U a).toScheme
                (E.restrict (U a).ι) hq).relProj ⟶
                ℙ(ULift.{u} (Fin (n a + 1)); (U a).toScheme),
              IsClosedImmersion j ∧
              j ≫ ℙ(ULift.{u} (Fin (n a + 1)); (U a).toScheme) ↘ (U a).toScheme =
                (@SymmetricAlgebraSheaf.gradedAlgebraData (U a).toScheme
                  (E.restrict (U a).ι) hq).relProjHom ∧
              IsHProjective (@SymmetricAlgebraSheaf.gradedAlgebraData (U a).toScheme
                (E.restrict (U a).ι) hq).relProjHom := by
  classical
  have : E.IsQuasicoherent := hE.1
  have : E.IsFiniteType := hE.2
  choose U hxU hU σ hσ using finite_generators_affine_neighborhood S E
  have hfin (x : S) : Finite (σ x).I := (hσ x).finite
  choose n s hs using fun x ↦ pad_finite_generators (E.restrict (U x).ι) (σ x)
  refine ⟨S, U, n, ?_, fun x ↦ ?_⟩
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · have : Epi ((E.restrict (U x).ι).freeHomEquiv.symm (s x)) := hs x
    have hq : (E.restrict (U x).ι).IsQuasicoherent := inferInstance
    have : (σ x).IsFiniteType := hσ x
    have ht := finiteType_of_finite_generators (E.restrict (U x).ι) (σ x)
    obtain ⟨j, hj, hjπ⟩ :=
      projectiveBundle_embedding_of_generators (U x).toScheme (E.restrict (U x).ι) (n x) (s x)
    refine ⟨hU x, s x, hs x, hq, ht, j, hj, hjπ, ?_⟩
    exact ⟨ULift.{u} (Fin (n x + 1)), inferInstance, j, hj, hjπ⟩

end AlgebraicGeometry
