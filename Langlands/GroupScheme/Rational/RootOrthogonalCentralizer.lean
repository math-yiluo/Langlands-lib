import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.LieProof

/-!
# Centralizers of cocharacters orthogonal to one root

For a split torus `S` in a group `G`, a character `α` and a cocharacter `ν` with
`⟨α, ν⟩ ≠ 0`, this module constructs a cocharacter `ζ₀` orthogonal to `α` such
that every relative root vanishing on `ζ₀` is a rational multiple of `α`. Its
dynamic centralizer lies in the dynamic centralizer of every cocharacter
orthogonal to `α`, and every relative root orthogonal to `ζ₀` remains a root of
the maximal split torus inside any representative of this centralizer.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Lattice

/-- Given `⟨α, ν⟩ ≠ 0`, there is a cocharacter `ζ₀` with `⟨α, ζ₀⟩ = 0` such that
every relative root `β` with `⟨β, ζ₀⟩ = 0` satisfies
`⟨α, ν⟩ • β = ⟨β, ν⟩ • α`. -/
theorem IsSplitTorus.exists_rootOrthogonalCocharacter [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (α : characterLattice S) (ν : cocharacterLattice S) :
    ∃ ζ₀ : cocharacterLattice S, latticePairing S α ζ₀ = 0 ∧
      ∀ β ∈ relativeRoots i, latticePairing S β ζ₀ = 0 →
        latticePairing S α ν • β = latticePairing S β ν • α := by
  classical
  let dev : characterLattice S → characterLattice S := fun β =>
    latticePairing S α ν • β - latticePairing S β ν • α
  let s : Set (characterLattice S) := dev '' relativeRoots i \ {0}
  have hs : s.Finite := ((hS.finite_relativeRoots i).image dev).sdiff
  have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx => hx.2
  obtain ⟨mu, hmu⟩ := hS.exists_pairings_ne_zero s hs hs0
  refine ⟨latticePairing S α ν • mu - latticePairing S α mu • ν, ?_, ?_⟩
  · simp only [map_sub, map_zsmul, smul_eq_mul]
    ring
  · intro β hβ hzero
    by_contra hne
    have hdev : dev β ∈ s := ⟨⟨β, hβ, rfl⟩, sub_ne_zero.mpr hne⟩
    apply hmu (dev β) hdev
    have h1 : latticePairing S (dev β) mu =
        latticePairing S α ν * latticePairing S β mu -
          latticePairing S β ν * latticePairing S α mu := by
      simp only [dev, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
    have h2 : latticePairing S β (latticePairing S α ν • mu - latticePairing S α mu • ν) =
        latticePairing S α ν * latticePairing S β mu -
          latticePairing S α mu * latticePairing S β ν := by
      simp only [map_sub, map_zsmul, smul_eq_mul]
    rw [h1]
    rw [h2] at hzero
    linarith

/-- A relative root proportional to `α` in the sense above vanishes on every
cocharacter orthogonal to `α`. -/
theorem latticePairing_eq_zero_of_smul_eq {α β : characterLattice S}
    {ν ζ : cocharacterLattice S} (hαν : latticePairing S α ν ≠ 0)
    (hβ : latticePairing S α ν • β = latticePairing S β ν • α)
    (hζ : latticePairing S α ζ = 0) : latticePairing S β ζ = 0 := by
  have h := congrArg (fun x => latticePairing S x ζ) hβ
  simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, hζ, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hαν

end Lattice

section Centralizer

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The dynamic centralizer of a root-orthogonal cocharacter lies in the dynamic
centralizer of every cocharacter orthogonal to the same root. -/
theorem dynamicCentralizer_le_of_rootOrthogonal (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) {α : characterLattice S} {ν ζ₀ : cocharacterLattice S}
    (hαν : latticePairing S α ν ≠ 0)
    (hζ₀ : ∀ β ∈ relativeRoots i, latticePairing S β ζ₀ = 0 →
      latticePairing S α ν • β = latticePairing S β ν • α)
    {ζ : cocharacterLattice S} (hζ : latticePairing S α ζ = 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom ζ₀ ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) :=
  dynamicCentralizer_le_of_root_zero_imp dynamicConnected hS i ζ₀ ζ fun β hβ h0 =>
    latticePairing_eq_zero_of_smul_eq hαν (hζ₀ β hβ h0) hζ

end Centralizer

section Roots

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {L : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom L.X.hom]
  (i : S.toGrp ⟶ G) (ζ₀ : cocharacterLattice S) {l : L ⟶ G}
  (hl : (Dynamic.centralizer (CommGroupScheme.groupHom ζ₀ ≫ i)).IsRepresentedBy l)
  (iL : S.toGrp ⟶ L) (hiL : iL ≫ l = i)

include hl

/-- Weight vectors of characters orthogonal to `ζ₀` lie in the tangent image of
the centralizer of `ζ₀`. -/
theorem weightSpace_le_range_of_pairing_eq_zero {β : characterLattice S}
    (hβ : latticePairing S β ζ₀ = 0) :
    weightSpace i β ≤ LinearMap.range (Lie.targetMapLinear l _) := by
  intro X hX
  apply (hl.mem_range_lieKernelHomLinear X).mpr
  apply (dynamicLie k G (CommGroupScheme.groupHom ζ₀ ≫ i) X.toMul).1.mpr
  have hcomp : ζ₀ ≫ β = Gm.powerHom _ 0 := by
    apply (gmEndEquiv k).injective
    simpa only [latticePairing_apply, Gm.powerHom, zero_smul, map_zero] using hβ
  have h := weightSpace_le_comp ζ₀ i β hX
  rwa [hcomp] at h

include hiL

/-- The differential identifies the weight spaces of characters orthogonal to
`ζ₀` in the centralizer with the ambient weight spaces. -/
theorem map_weightSpace_of_pairing_eq_zero {β : characterLattice S}
    (hβ : latticePairing S β ζ₀ = 0) :
    (weightSpace iL β).map (Lie.targetMapLinear l _) = weightSpace i β := by
  have : Mono l.hom.hom := hl.1
  apply le_antisymm
  · rintro X ⟨Y, hY, rfl⟩
    have h := lieKernelHomLinear_mem_weightSpace l iL β hY
    rwa [hiL] at h
  · intro X hX
    obtain ⟨Y, hY⟩ := weightSpace_le_range_of_pairing_eq_zero i ζ₀ hl hβ hX
    refine ⟨Y, ?_, hY⟩
    apply (lieKernelHomLinear_mem_weightSpace_iff l iL β Y).mp
    rw [hiL, hY]
    exact hX

/-- Every relative root orthogonal to `ζ₀` is a relative root of the torus inside
the centralizer of `ζ₀`. -/
theorem mem_relativeRoots_of_pairing_eq_zero {β : characterLattice S}
    (hβ : β ∈ relativeRoots i) (hβζ : latticePairing S β ζ₀ = 0) :
    β ∈ relativeRoots iL := by
  refine ⟨hβ.1, ?_⟩
  intro hbot
  have hmap := map_weightSpace_of_pairing_eq_zero i ζ₀ hl iL hiL hβζ
  rw [hbot, Submodule.map_bot] at hmap
  exact hβ.2 hmap.symm

end Roots

end Langlands.GroupScheme
