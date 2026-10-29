import Langlands.Cohomology.DivisibleSystem.HomSystem
import Langlands.Cohomology.DivisibleSystem.Invariants
import Langlands.Representation.Induction.QuotientAdjunction

/-!
# Hom systems out of invariants of `ℓ`-divisible systems

Let `S` be a normal subgroup of a group `G`, `T` an `ℓ`-divisible system of representations of
`G` and `W` an `ℓ`-divisible system of representations of `G ⧸ S`. Write `Inf W` for the
inflation `W.map (Rep.resFunctor (QuotientGroup.mk' S))` of `W` to `G`, and `T^S` for the
`ℓ`-divisible system `T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT` of
`S`-invariants of `T`, where `hT` states that the projections of `T` stay epimorphisms on
`S`-invariants.

Restriction of morphisms to the `S`-invariants (`homInvariantsRestriction` of the module
`QuotientAdjunction`) commutes with the transition maps of the Hom inverse systems of the module
`HomSystem` (`homTransition_homInvariantsRestriction`). It is therefore a morphism
`invariantsHomSystemHom` from the inverse system `m ↦ Hom(T m, Inf (W m))` to the inverse system
`m ↦ Hom((T m)^S, W m)`, and an isomorphism (`invariantsHomSystemIso`) when
`invariantsToCoinvariants` is bijective at every level of `T`. On the limits of these inverse
systems it is restriction to the `S`-invariants of morphisms of inverse systems
`T.tower ⟶ (Inf W).tower` (`towerInvariantsRestriction`, `ofHom_towerInvariantsRestriction`),
a linear equivalence under the same bijectivity hypothesis
(`towerInvariantsRestrictionEquiv`). For an `ℓ`-divisible system `K` of complexes,
`degreeInvariantsHomSystemIso` is the isomorphism for the degree `j` terms, with the degreewise
`S`-invariants system `K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK`.

Source: Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312: "We may replace `C^j_m(ẽ)` by
`C^j_m(ẽ)^{H_p}` in (4.10.2). Write
`T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`. To check the
Mittag-Leffler condition, we first need to study the maps (4.10.3)
`T_{m+1}(j, ẽ) → T_m(j, ẽ)` as `m` varies." In our reading the replacement has to be compatible
with the maps (4.10.3). This module states that compatibility for the Hom inverse systems of
`HomSystem`, with `T` in the role of the degree `j` terms and `W` in the role of the
coefficients; this correspondence, the definitions and the proofs are ours. The bijectivity
hypothesis is explicit. At a level `m` where `T m` is the compact induction of a trivial
representation from an open subgroup `H ≤ S` whose index in `S` is a unit, it is the published
`bijective_invariantsToCoinvariants_compactInduced`. Harris's modules `C^j_m(ẽ)` and
`T_m(j, ẽ)` and his maps (4.10.3) are not constructed here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite Langlands.Induction

universe w v u

namespace DivisibleSystem

section InvariantHomSystem

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (S : Subgroup G) [S.Normal] {ℓ : ℕ}
  (T : DivisibleSystem (Rep.{w} k G) ℓ)
  (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
    Epi ((Rep.quotientToInvariantsFunctor k S).map (T.projection h)))
  (W : DivisibleSystem (Rep.{w} k (G ⧸ S)) ℓ)

variable {k S T} in
/-- Restriction to the `S`-invariants commutes with the transition maps of the Hom inverse
systems: restricting the transition of `f : T m ⟶ Inf (W m)` gives the transition of the
restriction of `f`. -/
lemma homTransition_homInvariantsRestriction {m' m : ℕ} (h : m' ≤ m)
    (f : T.obj m ⟶ (W.map (Rep.resFunctor (QuotientGroup.mk' S))).obj m) :
    homTransition (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W h
        (homInvariantsRestriction (T.obj m) (W.obj m) f) =
      homInvariantsRestriction (T.obj m') (W.obj m')
        (homTransition T (W.map (Rep.resFunctor (QuotientGroup.mk' S))) h f) := by
  refine (homTransition_eq_iff _ W h _ _).2 ?_
  exact (homInvariantsRestriction_comp_left (T.projection h) _).symm.trans
    ((congrArg (homInvariantsRestriction (T.obj m) (W.obj m'))
      (projection_comp_homTransition T (W.map (Rep.resFunctor (QuotientGroup.mk' S))) h f)).trans
      (homInvariantsRestriction_comp_right f (W.projection h)))

/-- Restriction to the `S`-invariants, as a morphism from the inverse system
`m ↦ Hom(T m, Inf (W m))` to the inverse system `m ↦ Hom((T m)^S, W m)`. -/
def invariantsHomSystemHom :
    homSystem k T (W.map (Rep.resFunctor (QuotientGroup.mk' S))) ⟶
      homSystem k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W where
  app m := ModuleCat.ofHom (homInvariantsRestriction (T.obj m.unop) (W.obj m.unop))
  naturality m m' φ := by
    ext f
    exact (homTransition_homInvariantsRestriction hT W (leOfHom φ.unop) f).symm

/-- The component of `invariantsHomSystemHom` at `m` is `homInvariantsRestriction`. -/
lemma invariantsHomSystemHom_app_apply (m : ℕᵒᵖ)
    (f : T.obj m.unop ⟶ (W.map (Rep.resFunctor (QuotientGroup.mk' S))).obj m.unop) :
    (invariantsHomSystemHom k S T hT W).app m f =
      homInvariantsRestriction (T.obj m.unop) (W.obj m.unop) f :=
  rfl

/-- If `invariantsToCoinvariants` is bijective at every level of `T`, restriction to the
`S`-invariants is an isomorphism of the inverse systems `m ↦ Hom(T m, Inf (W m))` and
`m ↦ Hom((T m)^S, W m)`. -/
def invariantsHomSystemIso
    (hbij : ∀ m : ℕ, Function.Bijective (invariantsToCoinvariants (T.obj m).ρ S)) :
    homSystem k T (W.map (Rep.resFunctor (QuotientGroup.mk' S))) ≅
      homSystem k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W :=
  NatIso.ofComponents
    (fun m => (homInvariantsRestrictionEquiv (T.obj m.unop) (W.obj m.unop)
      (hbij m.unop)).toModuleIso)
    (fun φ => (invariantsHomSystemHom k S T hT W).naturality φ)

/-- The forward morphism of `invariantsHomSystemIso` is `invariantsHomSystemHom`. -/
lemma invariantsHomSystemIso_hom
    (hbij : ∀ m : ℕ, Function.Bijective (invariantsToCoinvariants (T.obj m).ρ S)) :
    (invariantsHomSystemIso k S T hT W hbij).hom = invariantsHomSystemHom k S T hT W := by
  refine NatTrans.ext (funext fun m => ?_)
  ext f
  exact homInvariantsRestrictionEquiv_apply (hbij m.unop) f

variable {k S T} in
/-- Restriction to the `S`-invariants of a morphism of inverse systems `T ⟶ Inf W`, as a
morphism of inverse systems `T^S ⟶ W`. -/
@[simps]
def towerInvariantsRestrictionApp
    (α : T.tower ⟶ (W.map (Rep.resFunctor (QuotientGroup.mk' S))).tower) :
    (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT).tower ⟶ W.tower where
  app m := homInvariantsRestriction (T.obj m.unop) (W.obj m.unop) (α.app m)
  naturality m m' φ :=
    (homInvariantsRestriction_comp_left (T.tower.map φ) (α.app m')).symm.trans
      ((congrArg (homInvariantsRestriction (T.obj m.unop) (W.obj m'.unop))
        (α.naturality φ)).trans (homInvariantsRestriction_comp_right (α.app m) (W.tower.map φ)))

/-- Restriction to the `S`-invariants, as a linear map from morphisms of inverse systems
`T ⟶ Inf W` to morphisms of inverse systems `T^S ⟶ W`. -/
@[simps]
def towerInvariantsRestriction :
    (T.tower ⟶ (W.map (Rep.resFunctor (QuotientGroup.mk' S))).tower) →ₗ[k]
      ((T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT).tower ⟶ W.tower) where
  toFun α := towerInvariantsRestrictionApp hT W α
  map_add' α β := by
    refine NatTrans.ext (funext fun m => ?_)
    exact (homInvariantsRestriction (T.obj m.unop) (W.obj m.unop)).map_add _ _
  map_smul' r α := by
    refine NatTrans.ext (funext fun m => ?_)
    exact (homInvariantsRestriction (T.obj m.unop) (W.obj m.unop)).map_smul _ _

/-- `towerInvariantsRestriction` is the map induced on the limits `homSystemCone` by
`invariantsHomSystemHom`. -/
lemma ofHom_towerInvariantsRestriction :
    (ModuleCat.ofHom (towerInvariantsRestriction k S T hT W) :
        (homSystemCone k T (W.map (Rep.resFunctor (QuotientGroup.mk' S)))).pt ⟶
          (homSystemCone k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W).pt) =
      (homSystemIsLimit k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W).map
        (homSystemCone k T (W.map (Rep.resFunctor (QuotientGroup.mk' S))))
        (invariantsHomSystemHom k S T hT W) := by
  refine (homSystemIsLimit k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT)
    W).hom_ext fun m => ?_
  refine Eq.trans ?_ (IsLimit.map_π (homSystemCone k T _)
    (homSystemIsLimit k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W)
    (invariantsHomSystemHom k S T hT W) m).symm
  ext α
  rfl

/-- If `invariantsToCoinvariants` is bijective at every level of `T`, restriction to the
`S`-invariants is a linear equivalence between morphisms of inverse systems `T ⟶ Inf W` and
`T^S ⟶ W`. -/
def towerInvariantsRestrictionEquiv
    (hbij : ∀ m : ℕ, Function.Bijective (invariantsToCoinvariants (T.obj m).ρ S)) :
    (T.tower ⟶ (W.map (Rep.resFunctor (QuotientGroup.mk' S))).tower) ≃ₗ[k]
      ((T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT).tower ⟶ W.tower) :=
  (IsLimit.conePointsIsoOfNatIso
    (homSystemIsLimit k T (W.map (Rep.resFunctor (QuotientGroup.mk' S))))
    (homSystemIsLimit k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W)
    (invariantsHomSystemIso k S T hT W hbij)).toLinearEquiv

/-- The underlying map of `towerInvariantsRestrictionEquiv` is `towerInvariantsRestriction`. -/
lemma towerInvariantsRestrictionEquiv_apply
    (hbij : ∀ m : ℕ, Function.Bijective (invariantsToCoinvariants (T.obj m).ρ S))
    (α : T.tower ⟶ (W.map (Rep.resFunctor (QuotientGroup.mk' S))).tower) :
    towerInvariantsRestrictionEquiv k S T hT W hbij α =
      towerInvariantsRestriction k S T hT W α := by
  refine NatTrans.ext (funext fun m => ?_)
  exact congrArg (fun g => g.hom α) (IsLimit.conePointsIsoOfNatIso_hom_comp
    (homSystemIsLimit k T (W.map (Rep.resFunctor (QuotientGroup.mk' S))))
    (homSystemIsLimit k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W)
    (invariantsHomSystemIso k S T hT W hbij) m)

end InvariantHomSystem

section Complexes

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (S : Subgroup G) [S.Normal] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (Rep.{w} k G) ℕ) ℓ)
  (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((Rep.quotientToInvariantsFunctor k S).map ((K.projection h).f q)))
  (W : DivisibleSystem (Rep.{w} k (G ⧸ S)) ℓ)

/-- For an `ℓ`-divisible system `K` of complexes and a degree `j`, restriction to the
`S`-invariants is an isomorphism of the inverse systems `m ↦ Hom(K_m^j, Inf (W m))` and
`m ↦ Hom((K_m^S)^j, W m)`, where `K^S` is the degreewise `S`-invariants system, provided
`invariantsToCoinvariants` is bijective on `K_m^j` for all `m`. -/
def degreeInvariantsHomSystemIso (j : ℕ)
    (hbij : ∀ m : ℕ, Function.Bijective (invariantsToCoinvariants ((K.obj m).X j).ρ S)) :
    homSystem k (K.degree j) (W.map (Rep.resFunctor (QuotientGroup.mk' S))) ≅
      homSystem k ((K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK).degree j) W :=
  invariantsHomSystemIso k S (K.degree j) (fun h => hK h j) W hbij

end Complexes

end DivisibleSystem

end Langlands.Cohomology
