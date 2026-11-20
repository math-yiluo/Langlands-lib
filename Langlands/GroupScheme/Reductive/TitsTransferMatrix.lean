import Langlands.GroupScheme.Reductive.InducedTensorRepresentation
import Langlands.GroupScheme.Reductive.TitsMaximalWeight
import Langlands.Algebra.CorestrictionTwistedFixed

/-! # The transfer identity for Tits obstructions in matrix form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix Langlands.Brauer
  Langlands.Algebra.KroneckerInduction Langlands.Algebra.CorestrictionTwistedFixed
  Langlands.BrauerCorestriction

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [IsGalois k K]
  (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

local instance titsTransferAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- **Transfer identity in matrix form.** Let `ρ` be a representation of `G_K` with top weight
`lam` (multiplicity one, all weights below it), and let invertible `Q h : ρ → ρ^h` intertwine
for `h ∈ Gal(K/E)`, where the `E`-algebra `twistedFixed Q` spans `M_n(K)`. Let `ε σ ∈ Gal(K/k)`
extend the `k`-embeddings `σ : E → N` (indexed by `Fin (m + 1)` through `e`). If the sum of
the star conjugates `ε σ ⋆ lam` is star-fixed, its Tits obstruction is the class of the tensor
descent (corestriction) of the central simple `E`-algebra `twistedFixed Q`. -/
theorem titsObstructionValue_eq_classOf_corCSAOf
    {E N : Type u} [Field E] [Field N] [Algebra k E] [Algebra k N] [Algebra E K] [Algebra N K]
    [IsScalarTower k E K] [IsScalarTower k N K] [FiniteDimensional k E] [FiniteDimensional k N]
    [IsGalois k N] [IsGalois E K]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {m : ℕ} (e : (E →ₐ[k] N) ≃ Fin (m + 1)) (ε : (E →ₐ[k] N) → (K ≃ₐ[k] K))
    (hε : ∀ σ x, ε σ (algebraMap E K x) = algebraMap N K (σ x))
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {lam : characterLattice d.toSplitPinning.torus} (hρ : d.toSplitPinning.HasTopWeight ρ lam)
    (Q : (K ≃ₐ[E] K) → Matrix n n K) (hQu : ∀ h, IsUnit (Q h))
    (hQ : ∀ h : K ≃ₐ[E] K, ρ.Intertwines (galoisTwist (h.restrictScalars k) ρ) (Q h))
    (hQspan : Submodule.span K
      ((twistedFixed Q : Subalgebra E (Matrix n n K)) : Set (Matrix n n K)) = ⊤)
    (hfix : d.IsStarFixedWeight (∑ i, (d.starAction (ε (e.symm i))).val • lam)) :
    d.titsObstructionValue hspan (∑ i, (d.starAction (ε (e.symm i))).val • lam) hfix =
      classOf (corCSAOf k E N (toCSA Q hQu (twistedFixed Q) le_rfl hQspan)) := by
  set I := inductionData e ε hε with hI
  set A := toCSA Q hQu (twistedFixed Q) le_rfl hQspan with hAdef
  have hA : Module.finrank E A = Fintype.card n * Fintype.card n :=
    finrank_eq Q hQu (twistedFixed Q) le_rfl hQspan
  let j : A →ₐ[E] Matrix n n K := (twistedFixed Q).val
  have hj : ∀ h a, Q h * j a = (j a).map h * Q h := fun h a => a.2 h
  rw [classOf_corCSAOf_eq A j e ε hε Q hj hQu hA]
  have hPiT := SplitPinning.HasTopWeight.piTensor
    (fun i => d.hasTopWeight_galoisTwist (ε (e.symm i)) hρ)
  have hPi := intertwines_galoisTwist_piTensor I Q ρ hQ
  exact d.titsObstructionValue_of_maximal hspan (inducedMatrix I Q) hPi
    (isUnit_inducedMatrix I Q hQu) _ le_rfl (span_twistedFixed_inducedMatrix j e ε hε Q hj hQu hA)
    (titsAlgebra_le_twistedFixed _ hPi) hfix hPiT.1 (fun mu hmu hsub => hPiT.eq_of_sub_mem hmu hsub)

end Langlands.GroupScheme.GaloisPinningData
