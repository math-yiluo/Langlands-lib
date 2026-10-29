import Langlands.Representation.Induction.InvariantRestriction

/-!
# Coinvariants, inflation and invariants for a normal subgroup

Let `S` be a normal subgroup of a group `G` and `k` a commutative ring. Mathlib provides the
functors `Rep.quotientToCoinvariantsFunctor k S` and `Rep.quotientToInvariantsFunctor k S` from
representations of `G` to representations of `G ⧸ S`, and inflation
`Rep.resFunctor (QuotientGroup.mk' S)` in the other direction. This module proves that
coinvariants are left adjoint to inflation (`coinvariantsInflationAdjunction`) and that
inflation is left adjoint to invariants (`inflationInvariantsAdjunction`), and packages the maps
`invariantsToCoinvariants` of the module `InvariantRestriction` into a natural transformation
`invariantsToCoinvariantsNatTrans` from invariants to coinvariants.

Restriction of a morphism `A ⟶ Inf W` to the `S`-invariants of `A` (`homInvariantsRestriction`)
is the component of this natural transformation at `A` followed by the morphism on
coinvariants corresponding to `f` under the first adjunction
(`homInvariantsRestriction_eq`). It is natural in `A` and `W`
(`homInvariantsRestriction_comp_left`, `homInvariantsRestriction_comp_right`), and a linear
equivalence when `invariantsToCoinvariants` is bijective for `A`
(`homInvariantsRestrictionEquiv`), in which case the component at `A` is an isomorphism
(`isIso_invariantsToCoinvariantsNatTrans_app`). This holds for the compact induction from an
open subgroup `H ≤ S` of a trivial representation when the index of `H` in `S` is a unit
(`isIso_invariantsToCoinvariantsNatTrans_app_compactInduced`).

Source: Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312: "We may replace `C^j_m(ẽ)` by
`C^j_m(ẽ)^{H_p}` in (4.10.2). Write
`T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`". The module
`InvariantRestriction` proves the algebra of this replacement for spaces of intertwining maps;
this module states it for morphisms in the categories `Rep`, in the form needed to compare
inverse systems of such morphisms. The adjunctions are standard; the definitions and proofs are
ours. Harris's modules `C^j_m(ẽ)` and the systems `T_m(j, ẽ)` are not constructed here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory

universe w v u

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (H : Subgroup G) [H.Normal]

/-- The inclusion of the `H`-invariants, as a morphism of representations of `G` after
inflating the representation of `G ⧸ H` along the quotient map. -/
@[simps]
def quotientInvariantsInclusion :
    Rep.quotientToInvariantsFunctor.{w} k H ⋙ Rep.resFunctor (QuotientGroup.mk' H) ⟶
      𝟭 (Rep.{w} k G) where
  app A := Rep.ofHom (A.ρ.quotientToInvariants_lift H)
  naturality _ _ _ := by
    ext
    rfl

end Langlands.Cohomology

namespace Langlands.Induction

open CategoryTheory

universe u v w uH uM

section Adjunctions

variable (k : Type u) {G : Type v} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

/-- The unit of the adjunction between coinvariants and inflation: the projection of a
representation of `G` to its `S`-coinvariants, inflated back to `G`. -/
def coinvariantsInflationUnit :
    𝟭 (Rep.{w} k G) ⟶
      Rep.quotientToCoinvariantsFunctor k S ⋙ Rep.resFunctor (QuotientGroup.mk' S) where
  app A := Rep.ofHom ((homCoinvariantsEquiv A.ρ S (A.ρ.quotientToCoinvariants S)).symm
    (Representation.IntertwiningMap.id _))
  naturality _ _ _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => rfl

/-- The counit of the adjunction between coinvariants and inflation: the `S`-coinvariants of the
inflation of a representation of `G ⧸ S` map back to it. -/
def coinvariantsInflationCounit :
    Rep.resFunctor (QuotientGroup.mk' S) ⋙ Rep.quotientToCoinvariantsFunctor k S ⟶
      𝟭 (Rep.{w} k (G ⧸ S)) where
  app W := Rep.ofHom (homCoinvariantsEquiv (W.ρ.comp (QuotientGroup.mk' S)) S W.ρ
    (Representation.IntertwiningMap.id _))
  naturality _ _ _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    Representation.Coinvariants.hom_ext rfl

/-- The `S`-coinvariants, as a representation of `G ⧸ S`, are left adjoint to inflation along
`G → G ⧸ S`. -/
def coinvariantsInflationAdjunction :
    Rep.quotientToCoinvariantsFunctor.{w} k S ⊣ Rep.resFunctor (QuotientGroup.mk' S) where
  unit := coinvariantsInflationUnit k S
  counit := coinvariantsInflationCounit k S
  left_triangle_components _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    Representation.Coinvariants.hom_ext rfl
  right_triangle_components _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => rfl

/-- The unit of the adjunction between inflation and invariants: a representation of `G ⧸ S`
is contained in the `S`-invariants of its inflation. -/
def inflationInvariantsUnit :
    𝟭 (Rep.{w} k (G ⧸ S)) ⟶
      Rep.resFunctor (QuotientGroup.mk' S) ⋙ Rep.quotientToInvariantsFunctor k S where
  app W := Rep.ofHom
    { toLinearMap := LinearMap.codRestrict _ LinearMap.id fun w s => by
        change W.ρ (QuotientGroup.mk (s : G)) w = w
        rw [(QuotientGroup.eq_one_iff (s : G)).mpr s.2, map_one]
        rfl
      isIntertwining' := fun q => by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact LinearMap.ext fun _ => Subtype.ext rfl }
  naturality _ _ _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => Subtype.ext rfl

/-- Inflation along `G → G ⧸ S` is left adjoint to the `S`-invariants, as a representation of
`G ⧸ S`. -/
def inflationInvariantsAdjunction :
    Rep.resFunctor.{w} (QuotientGroup.mk' S) ⊣ Rep.quotientToInvariantsFunctor k S where
  unit := inflationInvariantsUnit k S
  counit := Langlands.Cohomology.quotientInvariantsInclusion k S
  left_triangle_components _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => rfl
  right_triangle_components _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => Subtype.ext rfl

/-- The maps `invariantsToCoinvariants` from `S`-invariants to `S`-coinvariants, as a natural
transformation of functors to representations of `G ⧸ S`. -/
def invariantsToCoinvariantsNatTrans :
    Rep.quotientToInvariantsFunctor.{w} k S ⟶ Rep.quotientToCoinvariantsFunctor k S where
  app A := Rep.ofHom (invariantsToCoinvariants A.ρ S)
  naturality _ _ _ := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ => rfl

variable {k S}

/-- If `invariantsToCoinvariants` is bijective for `A`, the component of
`invariantsToCoinvariantsNatTrans` at `A` is an isomorphism. -/
theorem isIso_invariantsToCoinvariantsNatTrans_app (A : Rep.{w} k G)
    (h : Function.Bijective (invariantsToCoinvariants A.ρ S)) :
    IsIso ((invariantsToCoinvariantsNatTrans k S).app A) :=
  (Rep.mkIso ((invariantsToCoinvariants A.ρ S).ofBijective h)).isIso_hom

end Adjunctions

section Restriction

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G} [S.Normal]

/-- Restriction of a morphism `A ⟶ Inf W` to the `S`-invariants of `A`, as a morphism of
representations of `G ⧸ S`; the morphism form of `invariantsRestriction`. -/
def homInvariantsRestriction (A : Rep.{w} k G) (W : Rep.{w} k (G ⧸ S)) :
    (A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W) →ₗ[k]
      ((Rep.quotientToInvariantsFunctor k S).obj A ⟶ W) :=
  (Rep.homLinearEquiv _ _).symm.toLinearMap ∘ₗ invariantsRestriction A.ρ S W.ρ ∘ₗ
    (Rep.homLinearEquiv _ _).toLinearMap

/-- `homInvariantsRestriction f` is `f` on invariant vectors. -/
theorem homInvariantsRestriction_apply {A : Rep.{w} k G} {W : Rep.{w} k (G ⧸ S)}
    (f : A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W)
    (v : Representation.invariants (A.ρ.comp S.subtype)) :
    (homInvariantsRestriction A W f).hom v = f.hom v.1 :=
  rfl

/-- Restriction to invariants is the component of `invariantsToCoinvariantsNatTrans` followed by
the morphism on coinvariants corresponding to `f` under `coinvariantsInflationAdjunction`. -/
theorem homInvariantsRestriction_eq {A : Rep.{w} k G} {W : Rep.{w} k (G ⧸ S)}
    (f : A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W) :
    homInvariantsRestriction A W f = (invariantsToCoinvariantsNatTrans k S).app A ≫
      ((coinvariantsInflationAdjunction k S).homEquiv A W).symm f :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

/-- Restriction to invariants commutes with precomposition: restricting `g ≫ f` is the map
induced by `g` on invariants followed by the restriction of `f`. -/
theorem homInvariantsRestriction_comp_left {A A' : Rep.{w} k G} {W : Rep.{w} k (G ⧸ S)}
    (g : A' ⟶ A) (f : A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W) :
    homInvariantsRestriction A' W (g ≫ f) =
      (Rep.quotientToInvariantsFunctor k S).map g ≫ homInvariantsRestriction A W f :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

/-- Restriction to invariants commutes with postcomposition by the inflation of a morphism of
representations of `G ⧸ S`. -/
theorem homInvariantsRestriction_comp_right {A : Rep.{w} k G} {W W' : Rep.{w} k (G ⧸ S)}
    (f : A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W) (h : W ⟶ W') :
    homInvariantsRestriction A W' (f ≫ (Rep.resFunctor (QuotientGroup.mk' S)).map h) =
      homInvariantsRestriction A W f ≫ h :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

/-- If `invariantsToCoinvariants` is bijective for `A`, restriction to the `S`-invariants is a
linear equivalence between morphisms `A ⟶ Inf W` and morphisms from the `S`-invariants of `A`
to `W`. -/
def homInvariantsRestrictionEquiv (A : Rep.{w} k G) (W : Rep.{w} k (G ⧸ S))
    (h : Function.Bijective (invariantsToCoinvariants A.ρ S)) :
    (A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W) ≃ₗ[k]
      ((Rep.quotientToInvariantsFunctor k S).obj A ⟶ W) :=
  (Rep.homLinearEquiv A ((Rep.resFunctor (QuotientGroup.mk' S)).obj W)).trans
    ((invariantsRestrictionEquiv A.ρ S W.ρ h).trans
      (Rep.homLinearEquiv ((Rep.quotientToInvariantsFunctor k S).obj A) W).symm)

/-- `homInvariantsRestrictionEquiv` is `homInvariantsRestriction`. -/
theorem homInvariantsRestrictionEquiv_apply {A : Rep.{w} k G} {W : Rep.{w} k (G ⧸ S)}
    (h : Function.Bijective (invariantsToCoinvariants A.ρ S))
    (f : A ⟶ (Rep.resFunctor (QuotientGroup.mk' S)).obj W) :
    homInvariantsRestrictionEquiv A W h f = homInvariantsRestriction A W f :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

end Restriction

section CompactInduction

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k : Type u} {M : Type uM} [CommRing k] [AddCommGroup M] [Module k M]
variable {H S : Subgroup G} (hH : IsOpen (H : Set G)) (hHS : H ≤ S) [S.Normal]
  [(H.subgroupOf S).FiniteIndex]

include hH hHS in
/-- For `H ≤ S` open with `S` normal and the index of `H` in `S` a unit of `k`, the component
of `invariantsToCoinvariantsNatTrans` at the compact induction from `H` of a trivial
representation is an isomorphism. -/
theorem isIso_invariantsToCoinvariantsNatTrans_app_compactInduced
    (h : IsUnit ((H.subgroupOf S).index : k)) :
    IsIso ((invariantsToCoinvariantsNatTrans k S).app
      (Rep.of (compactInduced H (Representation.trivial k H M)))) :=
  isIso_invariantsToCoinvariantsNatTrans_app _
    (bijective_invariantsToCoinvariants_compactInduced hH hHS h)

end CompactInduction

end Langlands.Induction
