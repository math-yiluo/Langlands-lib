import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Absolute.RationalPointClosureProof
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.IdentityComponent
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Primes below a Borel coordinate kernel whose rational points form a solvable group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.BorelFieldExtension

section Points

/-- The prime of global functions vanishing at the image of a point is the preimage of the prime
of global functions vanishing at the point. -/
theorem toSpecΓ_asIdeal_apply {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    (X.toSpecΓ (f y)).asIdeal = Ideal.comap f.appTop.hom (Y.toSpecΓ y).asIdeal := by
  rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply]
  rfl

/-- A global function killed by `f` vanishes at every point in the image of `f`. -/
theorem ker_appTop_le_toSpecΓ {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    RingHom.ker f.appTop.hom ≤ (X.toSpecΓ (f y)).asIdeal := by
  rw [toSpecΓ_asIdeal_apply, RingHom.ker_eq_comap_bot]
  exact Ideal.comap_mono bot_le

/-- At the location of a point with values in a field, the vanishing prime is the kernel of the
point on global functions. -/
theorem toSpecΓ_asIdeal_of_field {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (CommRingCat.of k) ⟶ X) (a : Spec (CommRingCat.of k)) :
    (X.toSpecΓ (x a)).asIdeal = RingHom.ker x.appTop.hom := by
  rw [toSpecΓ_asIdeal_apply, RingHom.ker_eq_comap_bot]
  congr 1
  rw [← SpecMap_ΓSpecIso_hom, Spec.map_apply]
  refine le_bot_iff.1 fun r hr => ?_
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom r ∈ (a : PrimeSpectrum k).asIdeal := hr
  have hp : (a : PrimeSpectrum k).asIdeal.IsPrime := (a : PrimeSpectrum k).isPrime
  rw [@Ideal.eq_bot_of_prime _ _ _ hp, Ideal.mem_bot] at h0
  rw [Ideal.mem_bot]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
    (h0.trans (map_zero _).symm)

/-- A global function killed by `g` is killed by every composite `f ≫ g`. -/
theorem ker_appTop_le_comp {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ W) :
    RingHom.ker g.appTop.hom ≤ RingHom.ker (f ≫ g).appTop.hom := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]

end Points

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G B : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : B ⟶ G}

/-- Let `i : B ⟶ G` be a Borel subgroup of an affine group scheme of finite type over an
algebraically closed field, and let `𝔭` be a prime of global functions contained in the
coordinate kernel of `i`. If every rational point killing `𝔭` lies in a fixed solvable group `Γ`
of rational points, then `𝔭` is the coordinate kernel of `i`. -/
theorem coordinateKernel_le_of_solvable_points (hi : IsBorelSubgroup i)
    (𝔭 : Ideal Γ(G.X.left, ⊤)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≤ BorelExistence.coordinateKernel i)
    (Γ : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) [Group.IsSolvable Γ]
    (hΓ : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      𝔭 ≤ RingHom.ker x.left.appTop.hom → x ∈ Γ) :
    BorelExistence.coordinateKernel i ≤ 𝔭 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k B.X.left B.X.hom
  -- The closure `Z` of the locations of `Γ`.
  obtain ⟨Z, ζ, hζ, hZsm, hZrange⟩ := rationalPointClosureSubgroup k G Γ
  have : IsClosedImmersion ζ.hom.hom.left := hζ
  have : IsAffineHom Z.X.hom := by
    rw [← Over.w ζ.hom.hom]
    infer_instance
  -- The point `ξ` of `G` at which `𝔭` is the vanishing prime.
  let t := G.X.left.toSpecΓ
  obtain ⟨ξ, hξ⟩ := t.homeomorph.surjective ⟨𝔭, inferInstance⟩
  rw [Scheme.Hom.homeomorph_apply] at hξ
  have hspec : ∀ y, ξ ⤳ y ↔ 𝔭 ≤ (t y).asIdeal := by
    intro y
    rw [← t.homeomorph.isInducing.specializes_iff, Scheme.Hom.homeomorph_apply,
      Scheme.Hom.homeomorph_apply, hξ]
    exact (PrimeSpectrum.le_iff_specializes (⟨𝔭, inferInstance⟩ : PrimeSpectrum Γ(G.X.left, ⊤))
      (t y)).symm
  have hpt : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (t (x.left (IsLocalRing.closedPoint k))).asIdeal = RingHom.ker x.left.appTop.hom :=
    fun x => toSpecΓ_asIdeal_of_field x.left _
  -- Step 1: `ξ` lies on `Z`, by density of closed points in the closure of `ξ`.
  have hJ : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hξζ : ξ ∈ Set.range ζ.hom.hom.left := by
    have hcl : IsClosed (Set.range ζ.hom.hom.left) :=
      ζ.hom.hom.left.isClosedEmbedding.isClosed_range
    have hsub : closure {ξ} ∩ closedPoints G.X.left ⊆ Set.range ζ.hom.hom.left := by
      rintro p ⟨hp, hpc⟩
      let x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
        Over.homMk (pointOfClosedPoint G.X.hom p hpc) (pointOfClosedPoint_comp G.X.hom p hpc)
      have hxp : x.left (IsLocalRing.closedPoint k) = p :=
        pointOfClosedPoint_apply G.X.hom p hpc _
      have hx : x ∈ Γ := hΓ x (by
        rw [← hpt x, hxp]
        exact (hspec p).1 (specializes_iff_mem_closure.2 hp))
      rw [hZrange, ← hxp]
      exact subset_closure ⟨x, hx, rfl⟩
    have h1 : closure {ξ} ⊆ Set.range ζ.hom.hom.left := by
      rw [← closure_inter_closedPoints isClosed_closure]
      exact closure_minimal hsub hcl
    exact h1 (subset_closure rfl)
  -- Step 2: `B` factors through `Z`, since its rational points kill `𝔭`.
  have hBZ : (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≤
      (SubgroupFunctor.range ζ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    intro y hy
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.1 hy
    refine SubgroupFunctor.mem_range.2 ?_
    have hmem : a ≫ i.hom.hom ∈ Γ :=
      hΓ _ (h𝔭.trans (ker_appTop_le_comp a.left i.hom.hom.left))
    have hloc : (a ≫ i.hom.hom).left (IsLocalRing.closedPoint k) ∈
        Set.range ζ.hom.hom.left := by
      rw [hZrange]
      exact subset_closure ⟨_, hmem, rfl⟩
    obtain ⟨q, hq⟩ := hloc
    have hinj := ζ.hom.hom.left.isClosedEmbedding.injective
    have hqc : IsClosed {q} := by
      rw [← hinj.preimage_image {q}, Set.image_singleton, hq]
      exact (isClosed_singleton_rationalPoint (a ≫ i.hom.hom)).preimage
        ζ.hom.hom.left.continuous
    let z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X :=
      Over.homMk (pointOfClosedPoint Z.X.hom q hqc) (pointOfClosedPoint_comp Z.X.hom q hqc)
    have hz : z.left (IsLocalRing.closedPoint k) = q := pointOfClosedPoint_apply Z.X.hom q hqc _
    refine ⟨z, rationalPoint_ext ?_⟩
    exact (congrArg ζ.hom.hom.left hz).trans hq
  obtain ⟨a, ha⟩ := SubgroupFunctor.exists_factor_of_algClosed_points hζ hBZ
  -- Step 3: `B` factors through the identity component `Z⁰`, which is admissible.
  let g := IdentityComponent.factor Z a
  let j := identityComponentι Z ≫ ζ
  have hgj : g ≫ j = i := by
    simp only [g, j, IdentityComponent.factor_identityComponentι_assoc, ha]
  have hj : IsClosedSubgroup j := by
    change IsClosedImmersion ((identityComponentι Z).hom.hom.left ≫ ζ.hom.hom.left)
    infer_instance
  have hsolv : IsSolvableGroupScheme (identityComponent Z) := by
    rw [isSolvableGroupScheme_iff_isSolvable_points]
    have := isSolvable_pointClosureSubgroup (H := G) Γ
    have hmem : ∀ x, IsMonHom.monoidHom j.hom.hom (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x ∈
        pointClosureSubgroup G Γ := by
      intro x
      change (x ≫ j.hom.hom).left (IsLocalRing.closedPoint k) ∈
        closure (rationalPointImage G (Γ : Set _))
      rw [← hZrange]
      exact ⟨(identityComponentι Z).hom.hom.left (x.left (IsLocalRing.closedPoint k)), rfl⟩
    refine Group.isSolvable_of_isSolvable_injective
      (f := (IsMonHom.monoidHom j.hom.hom _).codRestrict (pointClosureSubgroup G Γ) hmem) ?_
    intro x y hxy
    have hxy' : x ≫ j.hom.hom = y ≫ j.hom.hom := congrArg Subtype.val hxy
    have : IsClosedImmersion j.hom.hom.left := hj
    have h' : x.left ≫ j.hom.hom.left = y.left ≫ j.hom.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, hxy']
    exact Over.OverMorphism.ext ((cancel_mono j.hom.hom.left).1 h')
  have : IsIso g := hi.maximal (identityComponent Z) j g hj inferInstance inferInstance hsolv hgj
  have hij : BorelExistence.coordinateKernel i ≤ BorelExistence.coordinateKernel j :=
    BorelExistence.coordinateKernel_le j i (inv g) (by rw [IsIso.inv_comp_eq, hgj])
  -- Step 4: `ξ` specializes to the identity, so it lies on `Z⁰`, hence on `B`.
  obtain ⟨ξ', rfl⟩ := hξζ
  have heB : i.hom.hom.left (IdentityComponent.identityPoint B) =
      IdentityComponent.identityPoint G := by
    simp only [IdentityComponent.identityPoint]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  have heZ : ζ.hom.hom.left (IdentityComponent.identityPoint Z) =
      IdentityComponent.identityPoint G := by
    simp only [IdentityComponent.identityPoint]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  have hξe : ζ.hom.hom.left ξ' ⤳ IdentityComponent.identityPoint G := by
    rw [hspec, ← heB]
    exact h𝔭.trans (ker_appTop_le_toSpecΓ _ _)
  have hξ'e : ξ' ⤳ IdentityComponent.identityPoint Z := by
    rw [← ζ.hom.hom.left.isClosedEmbedding.isInducing.specializes_iff, heZ]
    exact hξe
  have hξ'mem : ξ' ∈ Set.range (identityComponentι Z).hom.hom.left := by
    rw [IdentityComponent.range_identityComponentι]
    exact hξ'e.mem_open (IdentityComponent.isClopen_identitySet Z).isOpen
      mem_connectedComponent
  obtain ⟨w, rfl⟩ := hξ'mem
  have hw : t (j.hom.hom.left w) = ⟨𝔭, inferInstance⟩ := hξ
  have := ker_appTop_le_toSpecΓ j.hom.hom.left w
  rw [hw] at this
  exact hij.trans this

end Langlands.GroupScheme.BorelFieldExtension
