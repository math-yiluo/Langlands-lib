import Langlands.GroupScheme.Rational.StandardParabolicIntersections
import Langlands.GroupScheme.Descent.GaloisInvariantParabolics
import Mathlib.Data.Finset.Lattice.Fold

/-! # Galois-permuted finite families of standard parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G H : GroupScheme B} {Index : Type v}

/-- Preimages commute with arbitrary all-test intersections. -/
theorem intersection_comap (f : H ⟶ G) (P : Index → SubgroupFunctor G) :
    (intersection P).comap f = intersection (fun a => (P a).comap f) := by
  ext U x
  simp only [mem_comap, mem_intersection]

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  (G₀ : GroupScheme (Spec (CommRingCat.of F)))

omit [Field F] [Field L] [Algebra F L] in
/-- Canonical descent transport preserves all-test intersections. -/
theorem descentTransport_intersection
    {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    (G : GroupScheme B) (P : Index → SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    descentTransport b a ha G (intersection P) =
      intersection (fun j => descentTransport b a ha G (P j)) := by
  ext U x
  simp only [mem_descentTransport, mem_intersection]

/-- Actual Galois transport commutes with every all-test intersection. -/
theorem galoisTransport_intersection (σ : L ≃ₐ[F] L)
    (P : Index → SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G₀)) :
    galoisTransport F L G₀ σ (intersection P) =
      intersection (fun a => galoisTransport F L G₀ σ (P a)) := by
  exact descentTransport_intersection (algebraBaseMap F L) (galoisBaseMap F L σ)
    (galoisBaseMap_over F L σ) G₀ P

/-- Permuting the members of a family makes its actual intersection invariant. -/
theorem galoisTransport_intersection_eq_of_permutes (σ : L ≃ₐ[F] L)
    (P : Index → SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap F L)).obj G₀))
    (e : Index ≃ Index) (he : ∀ a, galoisTransport F L G₀ σ (P a) = P (e a)) :
    galoisTransport F L G₀ σ (intersection P) = intersection P := by
  rw [galoisTransport_intersection]
  ext U x
  simp only [mem_intersection, he]
  constructor
  · intro hx a
    simpa only [e.apply_symm_apply] using hx (e.symm a)
  · intro hx a
    exact hx (e a)

end SubgroupFunctor

section Standard

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- A finite standard intersection is indexed by the intersection of its
simple-root subsets, including the empty-family full-group case. -/
theorem mem_standardParabolic_finsetInf
    {Index : Type v} (s : Finset Index) (J : Index → Set (characterLattice T))
    (hJ : ∀ a ∈ s, J a ⊆ simpleRelativeRoots i ν)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X) :
    x ∈ (standardParabolic i ν (simpleRelativeRoots i ν ∩ s.inf J)).carrier U ↔
      ∀ a ∈ s, x ∈ (standardParabolic i ν (J a)).carrier U := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.inf_empty, Set.top_eq_univ, Set.inter_univ,
        (standardParabolicEndpoints k G hG T i hi ν hν).2.2.1,
        SubgroupFunctor.top_carrier, Subgroup.mem_top, Finset.notMem_empty,
        false_implies, implies_true]
  | @insert a s ha ih =>
      have hJa := hJ a (Finset.mem_insert_self _ _)
      have hJs : ∀ b ∈ s, J b ⊆ simpleRelativeRoots i ν :=
        fun b hb => hJ b (Finset.mem_insert_of_mem hb)
      have hroot : simpleRelativeRoots i ν ∩ (insert a s).inf J =
          J a ∩ (simpleRelativeRoots i ν ∩ s.inf J) := by
        rw [Finset.inf_insert]
        ext α
        change (α ∈ simpleRelativeRoots i ν ∧ α ∈ J a ∧ α ∈ s.inf J) ↔
          α ∈ J a ∧ α ∈ simpleRelativeRoots i ν ∧ α ∈ s.inf J
        exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩,
          fun h => ⟨hJa h.1, h.1, h.2.2⟩⟩
      rw [hroot, standardParabolic_inter i ν hG hi hν _ _ hJa Set.inter_subset_left]
      change (x ∈ (standardParabolic i ν (J a)).carrier U ∧
        x ∈ (standardParabolic i ν (simpleRelativeRoots i ν ∩ s.inf J)).carrier U) ↔ _
      rw [ih hJs]
      simp only [Finset.mem_insert, forall_eq_or_imp]

namespace Standard

variable {Index : Type v} [Fintype Index]

/-- The actual canonical inclusion representing a finite standard intersection. -/
def finiteParabolicIntersectionHom (J : Index → Set (characterLattice T)) :
    parabolicScheme i ν (simpleRelativeRoots i ν ∩ Finset.univ.inf J) ⟶ G :=
  parabolicHom i ν _

include hG hi hν in
theorem range_finiteParabolicIntersectionHom
    (J : Index → Set (characterLattice T)) (hJ : ∀ a, J a ⊆ simpleRelativeRoots i ν) :
    SubgroupFunctor.range (finiteParabolicIntersectionHom i ν J) =
      SubgroupFunctor.intersection (fun a => standardParabolic i ν (J a)) := by
  rw [show SubgroupFunctor.range (finiteParabolicIntersectionHom i ν J) =
    standardParabolic i ν (simpleRelativeRoots i ν ∩ Finset.univ.inf J) from
      (isRepresentedBy_parabolicHom i ν _).2]
  ext U x
  rw [SubgroupFunctor.mem_intersection,
    mem_standardParabolic_finsetInf i ν hG hi hν _ J (fun a _ => hJ a)]
  simp only [Finset.mem_univ, true_implies]

include hG hi hν in
theorem isParabolicSubgroup_finiteParabolicIntersectionHom
    (J : Index → Set (characterLattice T)) :
    IsParabolicSubgroup (finiteParabolicIntersectionHom i ν J) := by
  let I := simpleRelativeRoots i ν ∩ Finset.univ.inf J
  have hI : I ⊆ simpleRelativeRoots i ν := Set.inter_subset_left
  obtain ⟨ζ, hζ⟩ := (standardCocharacter k G hG T i hi ν hν I hI).1
  apply isParabolicSubgroup_of_range_eq_dynamicParabolic hG _
    (isClosedSubgroup_parabolicHom i ν I) (CommGroupScheme.groupHom ζ ≫ i)
  exact (isRepresentedBy_parabolicHom i ν I).2.trans
    ((standardCocharacter k G hG T i hi ν hν I hI).2 ζ hζ).1

include hG hi hν in
/-- Applying one ambient isomorphism to the finite intersection is the
all-test intersection of the identically transported standard inclusions. -/
theorem range_finiteParabolicIntersectionHom_comp_iso
    (J : Index → Set (characterLattice T)) (hJ : ∀ a, J a ⊆ simpleRelativeRoots i ν)
    (e : G ≅ G) :
    SubgroupFunctor.range (finiteParabolicIntersectionHom i ν J ≫ e.hom) =
      SubgroupFunctor.intersection
        (fun a => SubgroupFunctor.range (parabolicHom i ν (J a) ≫ e.hom)) := by
  rw [SubgroupFunctor.range_comp_iso,
    range_finiteParabolicIntersectionHom i ν hG hi hν J hJ,
    SubgroupFunctor.intersection_comap]
  congr 1
  funext a
  rw [SubgroupFunctor.range_comp_iso, (isRepresentedBy_parabolicHom i ν (J a)).2]

end Standard

end Standard

section Galois

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {s : S.toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of L))}
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X.hom]
  (i : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
  (ν : cocharacterLattice T)

/-- With a central maximal split torus over the ground field, a finite family
of standard parabolics transported by one ambient isomorphism cannot be
Galois-permuted unless every member is the full-group standard parabolic. -/
theorem IsMaximalSplitTorus.eq_simpleRelativeRoots_of_galoisPermuted
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s)
    (hG : IsConnectedReductive G)
    (hGL : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {Index : Type v} [Fintype Index] (J : Index → Set (characterLattice T))
    (hJ : ∀ a, J a ⊆ simpleRelativeRoots i ν)
    (e : (GroupScheme.baseChange (algebraBaseMap F L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (hperm : ∀ σ : L ≃ₐ[F] L, ∃ ρ : Index ≃ Index, ∀ a,
      SubgroupFunctor.range (radicalGaloisHom (Standard.parabolicHom i ν (J a) ≫ e.hom) σ) =
        SubgroupFunctor.range (Standard.parabolicHom i ν (J (ρ a)) ≫ e.hom)) :
    ∀ a, J a = simpleRelativeRoots i ν := by
  let p := Standard.finiteParabolicIntersectionHom i ν J
  have hp : IsParabolicSubgroup (p ≫ e.hom) :=
    (Standard.isParabolicSubgroup_finiteParabolicIntersectionHom i ν hGL hi hν J).comp_iso e
  have hr := Standard.range_finiteParabolicIntersectionHom_comp_iso i ν hGL hi hν J hJ e
  have hinv : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range (radicalGaloisHom (p ≫ e.hom) σ) =
        SubgroupFunctor.range (p ≫ e.hom) := by
    intro σ
    obtain ⟨ρ, hρ⟩ := hperm σ
    unfold radicalGaloisHom
    rw [← SubgroupFunctor.descentTransport_range]
    change SubgroupFunctor.galoisTransport F L G σ
      (SubgroupFunctor.range (p ≫ e.hom)) = _
    rw [hr]
    apply SubgroupFunctor.galoisTransport_intersection_eq_of_permutes G σ _ ρ
    intro a
    change SubgroupFunctor.descentTransport (algebraBaseMap F L)
      (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) G
        (SubgroupFunctor.range (Standard.parabolicHom i ν (J a) ≫ e.hom)) = _
    rw [SubgroupFunctor.descentTransport_range]
    exact hρ a
  have : IsIso (p ≫ e.hom) := hs.isIso_parabolic_of_galoisInvariant hc hG hp hinv
  have hpI : IsIso p := by
    have he : (p ≫ e.hom) ≫ e.inv = p := by simp
    rw [← he]
    infer_instance
  let I := simpleRelativeRoots i ν ∩ Finset.univ.inf J
  have htop : standardParabolic i ν I = ⊤ := by
    rw [← (Standard.isRepresentedBy_parabolicHom i ν I).2]
    change SubgroupFunctor.range p = ⊤
    calc
      SubgroupFunctor.range p =
          SubgroupFunctor.range ((asIso p).hom ≫ 𝟙 _) := by simp
      _ = SubgroupFunctor.range (𝟙 _) := SubgroupFunctor.range_iso_comp (asIso p) _
      _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id _).2
  have hI : I ⊆ simpleRelativeRoots i ν := Set.inter_subset_left
  have hfull : simpleRelativeRoots i ν ⊆ I :=
    ((standardParabolicOrder L _ hGL T i hi ν hν).1 _ _ (Set.Subset.refl _) hI).1.mpr
      (by
        rw [(standardParabolicEndpoints L _ hGL T i hi ν hν).2.2.1, htop])
  intro a
  apply Set.Subset.antisymm (hJ a)
  intro α hα
  exact (Finset.inf_le (Finset.mem_univ a) : Finset.univ.inf J ⊆ J a)
    (hfull hα).2

end Galois

end Langlands.GroupScheme
