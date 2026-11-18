import Langlands.GroupScheme.Reductive.TitsMaximalWeight
import Langlands.GroupScheme.Reductive.StarOrbitRootSums

/-! # Vanishing of the Tits obstruction on the root span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [IsGalois k K]

  (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

local instance titsRootVanishingAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The obstruction only depends on the weight. -/
theorem titsObstructionValue_congr {a b : characterLattice d.toSplitPinning.torus} (h : a = b)
    (ha : d.IsStarFixedWeight a) (hb : d.IsStarFixedWeight b) :
    d.titsObstructionValue hspan a ha = d.titsObstructionValue hspan b hb := by
  subst h
  rfl

/-- If the obstruction vanishes on every star-orbit sum of simple roots, it vanishes on every
star-fixed element of the integral root span. -/
theorem titsObstructionValue_eq_zero_of_mem_rootSpan_of_starOrbitSum
    (horbit : ∀ q : d.StarOrbit, d.titsObstructionValue hspan (d.starOrbitSum q)
      (d.isStarFixedWeight_starOrbitSum q) = 0)
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.toSplitPinning.rootDatum.rootSpan ℤ) (hfix : d.IsStarFixedWeight lam) :
    d.titsObstructionValue hspan lam hfix = 0 := by
  set S := AddSubgroup.closure (Set.range d.starOrbitSum) with hS
  set φ := d.titsObstructionOn hspan S (fun x hx => d.isStarFixedWeight_of_mem_closure hx)
    with hφdef
  have hφ : ∀ x (hx : x ∈ S), φ ⟨x, hx⟩ = 0 := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact horbit q
    | zero => exact φ.map_zero
    | add x y hx hy ihx ihy =>
      have h : (⟨x + y, S.add_mem hx hy⟩ : S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [h, map_add, ihx, ihy, add_zero]
    | neg x hx ih =>
      have h : (⟨-x, S.neg_mem hx⟩ : S) = -⟨x, hx⟩ := rfl
      rw [h, map_neg, ih, neg_zero]
  exact hφ lam (d.mem_closure_starOrbitSum hlam hfix)

/-- If the obstruction vanishes at a star-fixed weight `δ` and at every `δ - s_q`, it vanishes at
every star-orbit sum `s_q`. -/
theorem titsObstructionValue_starOrbitSum_eq_zero {δ : characterLattice d.toSplitPinning.torus}
    (hδ : d.IsStarFixedWeight δ) (h0 : d.titsObstructionValue hspan δ hδ = 0)
    (q : d.StarOrbit)
    (h1 : d.titsObstructionValue hspan (δ - d.starOrbitSum q)
      (d.isStarFixedWeight_sub hδ (d.isStarFixedWeight_starOrbitSum q)) = 0) :
    d.titsObstructionValue hspan (d.starOrbitSum q) (d.isStarFixedWeight_starOrbitSum q) =
      0 := by
  have h := d.titsObstructionValue_add hspan
    (d.isStarFixedWeight_sub hδ (d.isStarFixedWeight_starOrbitSum q))
    (d.isStarFixedWeight_starOrbitSum q)
  rw [d.titsObstructionValue_congr hspan (sub_add_cancel δ (d.starOrbitSum q)) _ hδ, h0, h1,
    zero_add] at h
  exact h.symm

/-- A star-fixed weight is a maximal weight of multiplicity one of a Galois-rational
representation of `G_K`. -/
def HasRationalMaximalWeight (nu : characterLattice d.toSplitPinning.torus) : Prop :=
  ∃ (N : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Nonempty N)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N),
    IsGaloisRational ρ ∧
      Module.finrank K (d.toSplitPinning.representationWeightSpace ρ nu) = 1 ∧
      ∀ mu, d.toSplitPinning.representationWeightSpace ρ mu ≠ ⊥ →
        mu - nu ∈ d.toSplitPinning.positiveRootMonoid → mu = nu

theorem titsObstructionValue_eq_zero_of_hasRationalMaximalWeight
    {nu : characterLattice d.toSplitPinning.torus} (hfix : d.IsStarFixedWeight nu)
    (h : d.HasRationalMaximalWeight nu) : d.titsObstructionValue hspan nu hfix = 0 := by
  obtain ⟨N, _, _, _, ρ, hρ, hmult, hmaximal⟩ := h
  exact d.titsObstructionValue_eq_zero_of_rational hspan hρ hfix hmult hmaximal

/-- Root-span vanishing (Tits 1971, Corollary 3.5), reduced to Galois-rational representations:
if a star-fixed weight `δ` and every `δ - s_q` (`s_q` a star-orbit sum of simple roots) are
maximal weights of multiplicity one of Galois-rational representations, the obstruction vanishes
on every star-fixed element of the integral root span. -/
theorem titsObstructionValue_eq_zero_of_mem_rootSpan {δ : characterLattice d.toSplitPinning.torus}
    (hδ : d.IsStarFixedWeight δ) (hδrat : d.HasRationalMaximalWeight δ)
    (hqrat : ∀ q : d.StarOrbit, d.HasRationalMaximalWeight (δ - d.starOrbitSum q))
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.toSplitPinning.rootDatum.rootSpan ℤ) (hfix : d.IsStarFixedWeight lam) :
    d.titsObstructionValue hspan lam hfix = 0 :=
  d.titsObstructionValue_eq_zero_of_mem_rootSpan_of_starOrbitSum hspan
    (fun q => d.titsObstructionValue_starOrbitSum_eq_zero hspan hδ
      (d.titsObstructionValue_eq_zero_of_hasRationalMaximalWeight hspan hδ hδrat) q
      (d.titsObstructionValue_eq_zero_of_hasRationalMaximalWeight hspan _ (hqrat q)))
    hlam hfix

end Langlands.GroupScheme.GaloisPinningData
