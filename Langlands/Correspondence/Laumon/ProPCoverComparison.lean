import Langlands.Correspondence.Laumon.ArtinSchreierComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Pro-`p` fundamental groups of affine schemes in characteristic `p`

Katz (1986), Proposition (1.4.2), Lemma (1.4.3) and (1.4.4)–(1.4.6), pp. 79–81, with the review
of pro-`p` groups in (2.3.4)–(2.3.8), pp. 95–97: for a connected affine `𝔽_p`-scheme `Z` the
`𝔽_p`-cohomology of `Z` is the continuous cohomology of `π₁(Z)` and vanishes in degrees `≥ 2`, so
the maximal pro-`p` quotient of `π₁(Z)` is a free pro-`p` group; a continuous homomorphism of
free pro-`p` groups is an isomorphism if and only if it induces an isomorphism on continuous
`𝔽_p`-characters; with the degree-one Artin–Schreier comparison this shows that pullback along
`Spec R((T⁻¹)) → Spec R[T]` is an equivalence on finite étale covers with `p`-group monodromy.
This module defines maximal pro-`p` quotients, pro-`p` groups, free pro-`p` groups and covers
with `p`-group monodromy, and states the three comparisons.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Henniart.Laumon

section ProP

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]

/-- The kernel of the maximal pro-`p` quotient: the intersection of the open normal subgroups
`U` of `G` with `G ⧸ U` a `p`-group. -/
def maximalProPKernel : Subgroup G where
  carrier := {g | ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → g ∈ U.toSubgroup}
  one_mem' U _ := U.toSubgroup.one_mem
  mul_mem' ha hb U hU := U.toSubgroup.mul_mem (ha U hU) (hb U hU)
  inv_mem' ha U hU := U.toSubgroup.inv_mem (ha U hU)

/-- The kernel of the maximal pro-`p` quotient is normal. -/
instance maximalProPKernel_normal : (maximalProPKernel p G).Normal :=
  ⟨fun n hn g U hU => U.isNormal'.conj_mem n (hn U hU) g⟩

/-- **The maximal pro-`p` quotient** `G(p)` of a topological group `G` (Katz (2.3.8)): the
quotient by `maximalProPKernel p G`, with the quotient topology. For a profinite group every
continuous homomorphism to a pro-`p` group factors uniquely through it. -/
abbrev maximalProPQuotient : Type _ := G ⧸ maximalProPKernel p G

/-- For a prime `p`, a topological group `G` is pro-`p` if it is compact, Hausdorff and totally
disconnected and its quotients by open normal subgroups are `p`-groups. -/
def IsProPGroup [Fact p.Prime] [IsTopologicalGroup G] : Prop :=
  CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧
    ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup)

/-- `G` is a **free pro-`p` group** (Katz (2.3.4)–(2.3.5)): a pro-`p` group with a family
`(x i)` converging to `1` (every open normal subgroup contains all but finitely many `x i`) such
that, for every finite `p`-group `H` and every family `(h i)` in `H` with finitely many
`h i ≠ 1`, there is a unique continuous homomorphism `G → H` (one with open kernel) sending each
`x i` to `h i`. This is the restricted free pro-`p` group on the index set, the restricted
coproduct of copies of `ℤ_p`; testing on finite `p`-groups suffices, a pro-`p` group being the
limit of its finite quotients. -/
def IsFreeProPGroup (G : Type u) [Group G] [TopologicalSpace G] [Fact p.Prime]
    [IsTopologicalGroup G] : Prop :=
  IsProPGroup p G ∧ ∃ (I : Type u) (x : I → G),
    (∀ U : OpenNormalSubgroup G, {i | x i ∉ U.toSubgroup}.Finite) ∧
    ∀ (H : Type u) [Group H] [Finite H], IsPGroup p H → ∀ h : I → H, {i | h i ≠ 1}.Finite →
      ∃! φ : G →* H, IsOpen (φ.ker : Set G) ∧ ∀ i, φ (x i) = h i

end ProP

section Covers

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The finite étale cover `E` of `Y` has **`p`-group monodromy** at the geometric point `t`
(Katz (1.2.1)): the image of `π₁(Y, t) = Aut (fiber t)` in the permutations of the fibre of `E`
at `t` is a `p`-group. -/
def HasPGroupMonodromy (p : ℕ) (t : Spec (.of Ω) ⟶ Y) (E : Y.FiniteEtale) : Prop :=
  IsPGroup p (MulAction.toPermHom (Aut (Scheme.FiniteEtale.fiber t))
    ((Scheme.FiniteEtale.fiber t).obj E)).range

end Covers

/-- The discrete group `ℤ/p`, lifted to a universe `u`, is a topological `ℤ/p`-module. -/
instance continuousSMul_zmod_ulift (p : ℕ) : ContinuousSMul (ZMod p) (ULift.{u} (ZMod p)) :=
  ⟨continuous_of_discreteTopology⟩

/-- **`𝔽_p`-cohomology of connected affine schemes** (Katz 1986, Lemma (1.4.3), p. 79, proved in
(1.4.6), pp. 80–81). Let `Z` be a connected affine scheme on which the prime `p` vanishes and
`z` a geometric point of `Z`. For every `q`, `Hᵠ(Z_ét, ℤ/p)` is isomorphic to the continuous
cohomology `Hᵠ(π₁(Z, z), 𝔽_p)` of `π₁(Z, z) = Aut (fiber z)` with trivial coefficients
(Mathlib's `continuousCohomology`), and the latter vanishes for `q ≥ 2`. -/
def AffineEtaleFundamentalGroupCohomologyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Z : Scheme.{u}) [IsAffine Z] [ConnectedSpace Z],
    (p : Γ(Z, ⊤)) = 0 →
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Z),
      (∀ q : ℕ, Nonempty (Sheaf.H (Z.constantZMod p) q ≃+
        continuousCohomology.{0, u + 1, 0} q (TopRep.of
          (ContRepresentation.trivial (ZMod p) (Aut (Scheme.FiniteEtale.fiber z))
            (ULift.{u + 1} (ZMod p)))))) ∧
      ∀ q : ℕ, 2 ≤ q → Subsingleton (continuousCohomology.{0, u + 1, 0} q (TopRep.of
          (ContRepresentation.trivial (ZMod p) (Aut (Scheme.FiniteEtale.fiber z))
            (ULift.{u + 1} (ZMod p)))))

/-- **Free pro-`p` groups** (Katz 1986, (2.3.7) and (2.3.8.1)–(2.3.8.2), pp. 96–97, after Shatz,
Theorem 15 and Proposition 23). Let `p` be a prime.

1. For a profinite group `G` with `H²(G, 𝔽_p) = 0` (continuous cohomology, trivial coefficients),
   the maximal pro-`p` quotient `G(p)` is a free pro-`p` group.
2. For a profinite group `G`, the continuous `𝔽_p`-characters of `G(p)` and of `G` agree: every
   continuous homomorphism `G → 𝔽_p` factors uniquely through `G → G(p)`.
3. A continuous homomorphism `φ : G₁ → G₂` of free pro-`p` groups is bijective if and only if
   precomposition with `φ` is a bijection from the continuous `𝔽_p`-characters of `G₂` to those of
   `G₁`, and surjective if and only if this precomposition is injective. -/
def FreeProPComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
        [T2Space G] [TotallyDisconnectedSpace G],
      Subsingleton (continuousCohomology 2 (TopRep.of
        (ContRepresentation.trivial (ZMod p) G (ULift.{u} (ZMod p))))) →
      IsFreeProPGroup p (maximalProPQuotient p G)) ∧
    (∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
        [T2Space G] [TotallyDisconnectedSpace G] (ψ : G →ₜ* Multiplicative (ZMod p)),
      ∃! χ : maximalProPQuotient p G →ₜ* Multiplicative (ZMod p),
        ∀ g : G, χ (QuotientGroup.mk g) = ψ g) ∧
    ∀ (G₁ G₂ : Type u) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂]
      [TopologicalSpace G₂] [IsTopologicalGroup G₂] (φ : G₁ →ₜ* G₂),
      IsFreeProPGroup p G₁ → IsFreeProPGroup p G₂ →
        (Function.Bijective φ ↔
          Function.Bijective fun χ : G₂ →ₜ* Multiplicative (ZMod p) => χ.comp φ) ∧
        (Function.Surjective φ ↔
          Function.Injective fun χ : G₂ →ₜ* Multiplicative (ZMod p) => χ.comp φ)

/-- **Covers with `p`-group monodromy of `Spec R[T]` and `Spec R((T⁻¹))`** (Katz 1986,
Proposition (1.4.2), p. 79). Let `p` be a prime and `R` a ring with connected spectrum in which
`p` vanishes, and let `f : Spec R((T⁻¹)) → Spec R[T]` be induced by `artinSchreierLaurentHom R`.
Then `Spec R[T]` and `Spec R((T⁻¹))` are connected, and for every geometric point `x` of
`Spec R((T⁻¹))`:

1. the map `π₁(Spec R((T⁻¹)), x) → π₁(Spec R[T], f ∘ x)` (`pullbackPathHom`) induces an
   isomorphism of maximal pro-`p` quotients;
2. pullback along `f` is fully faithful on finite étale covers of `Spec R[T]` with `p`-group
   monodromy, preserves `p`-group monodromy, and every finite étale cover of `Spec R((T⁻¹))` with
   `p`-group monodromy is isomorphic to the pullback of one of them. -/
def ArtinSchreierCoverComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R], (p : R) = 0 →
    ConnectedSpace (Spec (.of R)) →
      ConnectedSpace (Spec (.of (Polynomial R))) ∧ ConnectedSpace (Spec (.of (LaurentSeries R))) ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of (LaurentSeries R))),
        (∃ φ : maximalProPQuotient p (Aut (Scheme.FiniteEtale.fiber x)) →*
            maximalProPQuotient p (Aut (Scheme.FiniteEtale.fiber
              (x ≫ Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R))))),
          Function.Bijective φ ∧ ∀ g, φ (QuotientGroup.mk g) =
            QuotientGroup.mk (Scheme.FiniteEtale.pullbackPathHom
              (Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R))) x g)) ∧
        (∀ E E' : (Spec (.of (Polynomial R))).FiniteEtale,
          HasPGroupMonodromy p (x ≫ Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R))) E →
          HasPGroupMonodromy p (x ≫ Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R))) E' →
            Function.Bijective fun φ : E ⟶ E' =>
              (Scheme.FiniteEtale.pullback
                (Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R)))).map φ) ∧
        (∀ E : (Spec (.of (Polynomial R))).FiniteEtale,
          HasPGroupMonodromy p (x ≫ Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R))) E →
            HasPGroupMonodromy p x ((Scheme.FiniteEtale.pullback
              (Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R)))).obj E)) ∧
        ∀ D : (Spec (.of (LaurentSeries R))).FiniteEtale, HasPGroupMonodromy p x D →
          ∃ E : (Spec (.of (Polynomial R))).FiniteEtale,
            HasPGroupMonodromy p (x ≫ Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R))) E ∧
              Nonempty ((Scheme.FiniteEtale.pullback
                (Spec.map (CommRingCat.ofHom (artinSchreierLaurentHom R)))).obj E ≅ D)

end Langlands.Henniart.Laumon
