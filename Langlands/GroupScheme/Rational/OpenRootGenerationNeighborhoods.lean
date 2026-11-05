import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Canonical point neighbourhoods from finite ordered products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.RelativeRoot

/-- A subgroup open in another subgroup is the restriction of an ambient open
identity neighbourhood, without any continuity assumption on the group law. -/
theorem exists_open_restrict_subgroup
    {A : Type*} [Group A] [TopologicalSpace A]
    (R V : Subgroup A) (hV : IsOpen (V.subgroupOf R : Set R)) :
    ∃ C : Set A, IsOpen C ∧ 1 ∈ C ∧ ∀ x ∈ C, x ∈ R → x ∈ V := by
  obtain ⟨C, hC, hCV⟩ := IsInducing.subtypeVal.isOpen_iff.mp hV
  have h1 : (1 : R) ∈ Subtype.val ⁻¹' C :=
    (Set.ext_iff.mp hCV (1 : R)).mpr (V.subgroupOf R).one_mem
  refine ⟨C, hC, h1, ?_⟩
  intro x hx hxR
  have hx' : (⟨x, hxR⟩ : R) ∈ V.subgroupOf R :=
    (Set.ext_iff.mp hCV ⟨x, hxR⟩).mp hx
  exact hx'

section One

variable {B : Scheme.{u}} {G U : GroupScheme B} {n : ℕ}
    {H : Fin n → GroupScheme B}

/-- An ordered-product isomorphism compatible with an injective subgroup
inclusion sends the product identity to the identity, on every test scheme. -/
theorem orderedProductIso_inv_one
    (j : ∀ r, H r ⟶ G) (jU : U ⟶ G) [Mono jU.hom.hom]
    (e : (∏ᶜ H).X ≅ U.X)
    (he : e.hom ≫ jU.hom.hom = orderedMultiplication j)
    (T : Over B) :
    (1 : T ⟶ U.X) ≫ e.inv = (1 : T ⟶ (∏ᶜ H).X) := by
  have h1 : (1 : T ⟶ (∏ᶜ H).X) ≫ e.hom = (1 : T ⟶ U.X) := by
    apply (cancel_mono jU.hom.hom).1
    rw [Category.assoc, he, comp_orderedMultiplication]
    simp [orderedPoints]
  rw [← h1]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end One

section Neighborhood

variable (F : Type u) [CommRing F] [TopologicalSpace F]
    {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    {n : ℕ} (H : Fin n → GroupScheme (Spec (CommRingCat.of F)))
    (R : Fin n → SubgroupFunctor G) (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (R r).IsRepresentedBy (j r))
    (RU : SubgroupFunctor G) (jU : U ⟶ G)
    (hU : RU.IsRepresentedBy jU) (hcU : IsClosedSubgroup jU)
    (e : (∏ᶜ H).X ≅ U.X)
    (he : e.hom ≫ jU.hom.hom = orderedMultiplication j)

include H j hj jU hU hcU e he in
/-- Open subgroups of the actual factor carriers control an ambient open
identity neighbourhood restricted to the represented ordered-product subgroup.
Every topology in this result is the canonical affine rational-point topology
or its subspace topology. -/
theorem exists_open_restrict_orderedProduct :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (V : Fin n → Subgroup (rationalPoints G)) (K : Subgroup (rationalPoints G)),
      (∀ r, IsOpen ((V r).subgroupOf ((R r).carrier (Over.mk (𝟙 _))) :
        Set ((R r).carrier (Over.mk (𝟙 _))))) →
      (∀ r, V r ≤ K) →
      ∃ C : Set (rationalPoints G), IsOpen C ∧ 1 ∈ C ∧
        ∀ x ∈ C, x ∈ RU.carrier (Over.mk (𝟙 _)) → x ∈ K := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro V K hV hK
  have : IsClosedImmersion jU.hom.hom.left := hcU
  have : IsAffine U.X.left := isAffine_of_isAffineHom jU.hom.hom.left
  have : Mono jU.hom.hom := hU.1
  let : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
  choose O hO hO1 hOV using
    fun r => exists_open_restrict_subgroup
      ((R r).carrier (Over.mk (𝟙 _))) (V r) (hV r)
  let q (r : Fin n) : U.X ⟶ G.X :=
    e.inv ≫ (Pi.π H r).hom.hom ≫ (j r).hom.hom
  let W : Set (rationalPoints U) :=
    ⋂ r, (fun p : rationalPoints U => p ≫ q r) ⁻¹' O r
  have hW : IsOpen W := isOpen_iInter_of_finite fun r =>
    (hO r).preimage (continuous_rationalPointMap F (q r))
  have hW1 : (1 : rationalPoints U) ∈ W := by
    apply Set.mem_iInter.mpr
    intro r
    change (1 : rationalPoints U) ≫ q r ∈ O r
    dsimp only [q]
    rw [← Category.assoc, ← Category.assoc,
      orderedProductIso_inv_one j jU e he]
    simpa only [MonObj.one_comp] using hO1 r
  obtain ⟨C, hC, hCW⟩ :=
    (isEmbedding_rationalPointMap F jU.hom.hom).isInducing.isOpen_iff.mp hW
  have hC1 : (1 : rationalPoints G) ∈ C := by
    have : (1 : rationalPoints U) ∈
        (fun p : rationalPoints U => p ≫ jU.hom.hom) ⁻¹' C := by
      rw [hCW]
      exact hW1
    simpa only [Set.mem_preimage, MonObj.one_comp] using this
  refine ⟨C, hC, hC1, ?_⟩
  intro x hx hxU
  let p := (hU.pointsEquiv (Over.mk (𝟙 _))).symm ⟨x, hxU⟩
  have hpx : p ≫ jU.hom.hom = x :=
    hU.pointsEquiv_symm_comp ⟨x, hxU⟩
  have hpW : p ∈ W := by
    rw [← hCW]
    change p ≫ jU.hom.hom ∈ C
    rwa [hpx]
  have hpO : ∀ r, p ≫ q r ∈ O r := Set.mem_iInter.mp hpW
  have hpR : ∀ r, p ≫ q r ∈ (R r).carrier (Over.mk (𝟙 _)) := by
    intro r
    exact (hj r).pointsEquiv (Over.mk (𝟙 _))
      (p ≫ e.inv ≫ (Pi.π H r).hom.hom) |>.property
  have hpK : ∀ r, p ≫ q r ∈ K :=
    fun r => hK r (hOV r _ (hpO r) (hpR r))
  have hfactor : x =
      orderedPoints j (finiteProductPointsEquiv H (Over.mk (𝟙 _)) (p ≫ e.inv)) := by
    rw [← comp_orderedMultiplication, ← he]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hpx.symm
  rw [hfactor]
  apply K.list_prod_mem
  intro y hy
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
  exact hpK r

end Neighborhood

/-- The canonical point-neighbourhood consequence of a compatible finite
ordered-product isomorphism, with all structural premises retained. -/
def OrderedProductNeighborhoodStatement : Prop :=
  ∀ (F : Type u) [CommRing F] [TopologicalSpace F]
    {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    {n : ℕ} (H : Fin n → GroupScheme (Spec (CommRingCat.of F)))
    (R : Fin n → SubgroupFunctor G) (j : ∀ r, H r ⟶ G)
    (_hj : ∀ r, (R r).IsRepresentedBy (j r))
    (RU : SubgroupFunctor G) (jU : U ⟶ G)
    (_hU : RU.IsRepresentedBy jU) (_hcU : IsClosedSubgroup jU)
    (e : (∏ᶜ H).X ≅ U.X)
    (_he : e.hom ≫ jU.hom.hom = orderedMultiplication j),
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (V : Fin n → Subgroup (rationalPoints G)) (K : Subgroup (rationalPoints G)),
      (∀ r, IsOpen ((V r).subgroupOf ((R r).carrier (Over.mk (𝟙 _))) :
        Set ((R r).carrier (Over.mk (𝟙 _))))) →
      (∀ r, V r ≤ K) →
      ∃ C : Set (rationalPoints G), IsOpen C ∧ 1 ∈ C ∧
        ∀ x ∈ C, x ∈ RU.carrier (Over.mk (𝟙 _)) → x ∈ K

/-- The generic canonical point-neighbourhood statement follows from the
inverse-coordinate construction. -/
theorem orderedProductNeighborhood : OrderedProductNeighborhoodStatement.{u} := by
  intro F _ _ G U _ n H R j hj RU jU hU hcU e he
  exact exists_open_restrict_orderedProduct F H R j hj RU jU hU hcU e he

end Langlands.GroupScheme.RelativeRoot
