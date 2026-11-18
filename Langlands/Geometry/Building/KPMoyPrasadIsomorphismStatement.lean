import Langlands.Geometry.Building.KPLieFiltration
import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.KPWeaklyInducedTorus
import Langlands.Geometry.Building.ValuationBuildingAxioms

/-!
# KP Theorem 13.5.1 (1), the Moy–Prasad isomorphism, on supplied data

For `0 < r ≤ s` satisfying one of the three alternatives of KP §13.5, the abstract abelian
groups `P_{x,r} / P_{x,s}` and `𝔤_{x,r} / 𝔤_{x,s}` are isomorphic. The statement is posed for
supplied filtrations `Z(F)_r`, `z_r` and `u_ψ`. It assumes the corresponding isomorphisms for
`Z` and for the root blocks, which KP obtain from the minimal congruent filtration
(Propositions B.6.9, B.10.16, B.10.17) and from Propositions C.5.1 and A.5.19. It also assumes
that `Z(F)_r` is double-root commutator friendly, the premise under which the Library proves
`[P_{x,r}, P_{x,r}] ⊆ P_{x,2r}` (KP Proposition 13.2.5(4)).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

/-- `H₁ / H₂ ≅ g₁ / g₂` as abstract groups, for subgroups `H₂ ≤ H₁` of a group and additive
subgroups `g₂ ≤ g₁` of an abelian group: some surjective homomorphism
`H₁ → g₁ / g₂` has kernel `H₂`. It is stated without quotient groups by `H₂`, which need no
normality instance this way. -/
def HasMoyPrasadQuotientIso {Γ M : Type*} [Group Γ] [AddCommGroup M]
    (H₁ H₂ : Subgroup Γ) (g₁ g₂ : AddSubgroup M) : Prop :=
  ∃ φ : H₁ →* Multiplicative (g₁ ⧸ g₂.addSubgroupOf g₁),
    Function.Surjective φ ∧ φ.ker = H₂.subgroupOf H₁

/-- The three alternatives of KP §13.5 for `0 < r ≤ s`:
(1) the maximally split maximal torus of `G_K` is weakly induced and `s ≤ 2r`;
(2) `r = r₀ + n` with `0 ≤ r₀ < 1` and `n` a positive integer, and `s ≤ r₀ + 2n`;
(3) `s ≤ 2r ≤ r + 1`. -/
def MoyPrasadAlternative (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    (r s : NNReal) : Prop :=
  (HasWeaklyInducedMaximallySplitTorus F G ∧ s ≤ 2 * r) ∨
    (∃ (r₀ : NNReal) (n : ℕ), r₀ < 1 ∧ 0 < n ∧ r = r₀ + n ∧ s ≤ r₀ + 2 * n) ∨
    (s ≤ 2 * r ∧ 2 * r ≤ r + 1)

namespace ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} (L : P.LieFiltrationData)

/-- The Lie side of the root block of `a` at depth `r`: `u_{a,x,r} + u_{2a,x,r}`, the second
summand being `0` when `2a` is not a relative root. -/
def rootBlockLie (x : P.Apartment) (α : relativeRoots P.i) (r : NNReal) :
    Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  L.rootLie x α r ⊔ ⨆ (β : relativeRoots P.i) (_ : β.1 = 2 • α.1), L.rootLie x β r

end ParahoricBuildingData.LieFiltrationData

/-- KP Theorem 13.5.1 (1) for supplied data, without the compatibility with unramified
extensions. Let `P` satisfy the apartment axioms and `Zf` the filtration axioms and the
double-root commutator condition, and let `L` supply the lattices `z_r` and `u_ψ`. Let `x` be a point of the apartment and `0 < r ≤ s`
satisfy one of the three alternatives of KP §13.5. Assume `Z(F)_r / Z(F)_s ≅ z_r / z_s`, and
for every non-divisible relative root `a` the isomorphism of the root block
`U_{a,x,r} U_{2a,x,r} / U_{a,x,s} U_{2a,x,s} ≅ (u_{a,x,r} + u_{2a,x,r}) / (u_{a,x,s} + u_{2a,x,s})`.
Then `P_{x,r} / P_{x,s} ≅ 𝔤_{x,r} / 𝔤_{x,s}` as abstract abelian groups. -/
def MoyPrasadIsomorphismStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration) (L : P.LieFiltrationData),
    P.SatisfiesApartmentAxioms → Zf.SatisfiesFiltrationAxioms →
      Zf.IsDoubleRootCommutatorFriendly →
      ∀ (x : P.Apartment) (r s : NNReal), 0 < r → r ≤ s → MoyPrasadAlternative F G r s →
        HasMoyPrasadQuotientIso (Zf.filtration r) (Zf.filtration s)
          (L.centralizerLie r).toAddSubgroup (L.centralizerLie s).toAddSubgroup →
        (∀ α : relativeRoots P.i, (∀ β : relativeRoots P.i, α.1 ≠ 2 • β.1) →
          HasMoyPrasadQuotientIso
            (Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (r : ℝ)) α.1))
            (Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (s : ℝ)) α.1))
            (L.rootBlockLie x α r).toAddSubgroup (L.rootBlockLie x α s).toAddSubgroup) →
        HasMoyPrasadQuotientIso (Zf.moyPrasad x r) (Zf.moyPrasad x s)
          (L.lieFiltration x r).toAddSubgroup (L.lieFiltration x s).toAddSubgroup

end Langlands.Geometry.Building
