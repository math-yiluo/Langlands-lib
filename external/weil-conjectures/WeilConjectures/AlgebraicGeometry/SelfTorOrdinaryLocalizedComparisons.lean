/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.SelfTorNonpositiveFlatSections
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.QuotientResolutionTensorComparison
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Chosen-lift affine sections of ordinary tensor

Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9 and 00LS.
(blueprint: new-h3-self-tor-ordinary-localized-comparisons). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry



-- The cone-and-square arguments below are the generic-site proofs already used in
-- OpenKFlatTensorHomologyComparison. Its public theorem works on the localized site;
-- here the same proved argument is needed directly on the ambient scheme site.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quasiIso_of_commuting_square
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {A B C D : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (k : C ⟶ D)
    (hf : QuasiIso f) (hg : QuasiIso g) (hh : QuasiIso h)
    (comm : f ≫ h = g ≫ k) : QuasiIso k := by
  have := hf
  have := hg
  have := hh
  have hcomp : QuasiIso (g ≫ k) := by
    rw [← comm]
    infer_instance
  have := hcomp
  exact quasiIso_of_comp_left g k

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kFlat_tensor_right_of_quasiIso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {E E' K : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso α K (curriedTensor _))

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kFlat_tensor_left_of_quasiIso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {K L L' : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : L ⟶ L') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem site_kFlat_tensor_quasiIso
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    {R : Sheaf J CommRingCat.{u}}
    {E E' N : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (α : E ⟶ E')
    (hα : QuasiIso α)
    (hE : E.IsKFlatTensor)
    (hE' : E'.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory R
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory R
  obtain ⟨K, s, hK, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution N
  let f := HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ)
  let g := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor _) (.up ℤ)
  let h := HomologicalComplex.mapBifunctorMap (𝟙 E') s (curriedTensor _) (.up ℤ)
  let k := HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ)
  apply quasiIso_of_commuting_square f g h k
  · exact kFlat_tensor_right_of_quasiIso α hα hK
  · exact kFlat_tensor_left_of_quasiIso s hs hE
  · exact kFlat_tensor_left_of_quasiIso s hs hE'
  · change ((curriedTensor _).map₂CochainComplex.map α).app K ≫
        ((curriedTensor _).map₂CochainComplex.obj E').map s =
      ((curriedTensor _).map₂CochainComplex.obj E).map s ≫
        ((curriedTensor _).map₂CochainComplex.map α).app N
    exact (((curriedTensor _).map₂CochainComplex.map α).naturality s).symm


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two K-flat resolutions of the same complex give isomorphic tensor homology.
The common roof is taken only in the derived category, never by a chain inverse.
Source: Stacks Project, Tags 06YB and 06YT. -/
private theorem tensor_homology_iso_of_resolutions
    (Y : Scheme.{u})
    (E K N T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (r : E ⟶ T) (q : K ⟶ T) (hE : E.IsKFlatTensor) (hK : K.IsKFlatTensor)
    (hr : QuasiIso r) (hq : QuasiIso q) (j : ℤ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    Nonempty ((CochainComplex.mapBifunctor E N (curriedTensor _)).homology j ≅
      (CochainComplex.mapBifunctor K N (curriedTensor _)).homology j) := by
  let M := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard M
  let D := DerivedCategory.Q (C := M)
  have : QuasiIso r := hr
  have : QuasiIso q := hq
  let e : D.obj E ≅ D.obj K := asIso (D.map r) ≪≫ (asIso (D.map q)).symm
  obtain ⟨L, a, ha, b, he⟩ := DerivedCategory.right_fac e.hom
  have : IsIso (D.map a) := ha
  have ha' : QuasiIso a := (DerivedCategory.isIso_Q_map_iff_quasiIso M a).1 ha
  have hb : IsIso (D.map b) := by
    have hb' : D.map b = D.map a ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [hb']
    infer_instance
  have hb' : QuasiIso b := (DerivedCategory.isIso_Q_map_iff_quasiIso M b).1 hb
  obtain ⟨F, s, hF, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution L
  have : QuasiIso a := ha'
  have : QuasiIso b := hb'
  have : QuasiIso s := hs
  have hsa : QuasiIso (s ≫ a) := inferInstance
  have hsb : QuasiIso (s ≫ b) := inferInstance
  let := SheafOfModules.monoidalCategory Y.sheaf
  let α := HomologicalComplex.mapBifunctorMap (s ≫ a) (𝟙 N) (curriedTensor _) (.up ℤ)
  let β := HomologicalComplex.mapBifunctorMap (s ≫ b) (𝟙 N) (curriedTensor _) (.up ℤ)
  have : QuasiIso α := site_kFlat_tensor_quasiIso (s ≫ a) hsa hF hE
  have : QuasiIso β := site_kFlat_tensor_quasiIso (s ≫ b) hsb hF hK
  exact ⟨(asIso (HomologicalComplex.homologyMap α j)).symm ≪≫
    asIso (HomologicalComplex.homologyMap β j)⟩


/-- Specialize the functorial flat replacement to one nonpositive complex. -/
private theorem exists_nonpositive_flat_quasiIso (Y : Scheme.{u})
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : ∀ j : ℤ, 0 < j → IsZero (T.X j)) :
    ∃ (E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (r : E ⟶ T),
      (∀ j : ℤ, SheafOfModules.IsFlat (E.X j)) ∧
      (∀ j : ℤ, 0 < j → IsZero (E.X j)) ∧ QuasiIso r := by
  obtain ⟨F, ε, hF⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology Y.carrier) Y.sheaf 0
  exact ⟨F.obj ⟨T, hT⟩, ε.app ⟨T, hT⟩,
    (hF ⟨T, hT⟩).1, (hF ⟨T, hT⟩).2.1, (hF ⟨T, hT⟩).2.2.2⟩


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary affine tensor comparison is compatible with one augmented algebraic
comparison for each basic inclusion. Independence of the supplied comparison is not
part of this statement.

Source: Stacks Project, Tag 08DX(2), affine calculation, Tags 06YG and 06YB for
K-flat comparison, Tag 01I9 for affine sections, and Tag 00LS(1) for existence of lifts.
(blueprint: new-h3-self-tor-ordinary-localized-comparisons).

Proof: Apply the functorial bounded-above flat replacement to B[0], which
vanishes in positive degrees. It supplies r:E -> B[0], with E nonpositive
and termwise flat. Bounded-above flatness makes E K-flat. The new bounded
chart lemma supplies its affine coordinates and restriction formula for
supplied augmented algebraic comparison maps.

Compare E and K over B[0] in the derived category. A common roof gives two
quasi-isomorphisms from a common complex; replace that complex by a K-flat
resolution F. Both maps F -> E and F -> K remain quasi-isomorphisms after
tensoring with B[0]. Here the proof uses a K-flat replacement of B[0] in a
commuting tensor square: tensoring a quasi-isomorphism with a K-flat factor
is a quasi-isomorphism by the cone criterion, and the other two sides are
quasi-isomorphisms for the same reason. Two-of-three proves the fourth side.
Taking homology and inverting one leg gives an isomorphism of sheaves
H^{-n}(E tensor B[0]) -> H^{-n}(K tensor B[0]). Compose every E-coordinate
with its induced linear equivalence on sections to obtain c_U.

For a basic inclusion, ideal restriction gives the containment required by
exists_quotient_resolution_tensor_comparison. Apply it to the two chosen
projective resolutions to construct psi, a, and k and their three equations.
The bounded chart lemma gives their restriction equation for E. Naturality
of the homology sheaf isomorphism transports this equation to K. No chain
inverse, coherence of a chosen family of chain lifts, or data definition
from a mere existence assertion is introduced. The construction covers zero
rings, the zero quotient, degree zero, and empty basic opens. -/
theorem exists_selfTor_ordinary_localized_comparisons
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj B)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).mapHomologicalComplex (.down ℕ)).obj
            (projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
              ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).complex).homology n) ≃ₗ[Γ(Y, U.1)]
              Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
          let A := (Γ(Y, U.1) : Type u)
          let C := (Γ(Y, V.1) : Type u)
          let I := i.ker.ideal U
          let J := i.ker.ideal V
          let φ := (Y.presheaf.map (homOfLE h).op).hom
          let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
          let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          ∃ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) ∧
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) ∧
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  classical
  intro B S Q
  let T := S.obj B
  have hT : ∀ j : ℤ, 0 < j → IsZero (T.X j) := by
    intro j hj
    exact HomologicalComplex.isZero_single_obj_X _ _ _ j (by omega)
  rcases exists_nonpositive_flat_quasiIso Y T hT with ⟨E, r, hEr⟩
  have hE : E.IsKFlatTensor := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    Y.toRingedSpace E ⟨0, hEr.2.1⟩ hEr.1
  let := SheafOfModules.monoidalCategory Y.sheaf
  rcases tensor_homology_iso_of_resolutions Y E K T T r q hE hK hEr.2.2 hq (-(n : ℤ)) with ⟨e⟩
  rcases exists_selfTor_nonpositive_flat_sections i E r hEr.2.1 hEr.1 hEr.2.2 n with ⟨d, hd⟩
  refine ⟨fun U ↦ (d U).trans (Scheme.Modules.appLinearEquivOfIso e U.1), ?_⟩
  intro V U h hbasic A C I J φ PU PV TA TC
  have hI : ∀ x ∈ I, φ x ∈ J := by
    intro x hx
    exact i.ker.ideal_le_comap_ideal h hx
  refine (exists_quotient_resolution_tensor_comparison A C I J φ hI PU PV).imp
    fun ψ ↦ Exists.imp fun a ↦ Exists.imp fun k hlift ↦ ?_
  refine ⟨hlift.1, hlift.2.1, hlift.2.2, ?_⟩
  intro e' x
  have hn := hd V U h hbasic ψ a k hlift.1 hlift.2.1 hlift.2.2 x
  have hs := PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op (d U x)
  change _ = e.hom.val.app (op V.1) _
  exact hs.symm.trans (congrArg (e.hom.val.app (op V.1)) hn)


end AlgebraicGeometry
