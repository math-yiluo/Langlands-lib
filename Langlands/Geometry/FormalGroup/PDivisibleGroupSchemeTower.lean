import Langlands.Geometry.FormalGroup.ScalarTorsionMultiplication
import Langlands.GroupScheme.Cartier.FiniteDualGeometry
import Langlands.GroupScheme.Cartier.FiniteDualSpectrum

/-! # A p-divisible group through its actual finite group scheme tower -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands

/-- A tower of finite locally free group schemes with the scalar factorization
and fppf short exact sequences of a p-divisible group. -/
structure PDivisibleGroup (R : CommRingCat.{v}) (p : ℕ) [Fact p.Prime] where
  inclusions : ℕ ⥤ CommGroupScheme (Spec R)
  transfer : ∀ {m n : ℕ}, (m ⟶ n) → (inclusions.obj n ⟶ inclusions.obj m)
  transfer_id : ∀ n : ℕ, transfer (𝟙 n) = 𝟙 (inclusions.obj n)
  transfer_comp : ∀ {l m n : ℕ} (i : l ⟶ m) (j : m ⟶ n),
    transfer (i ≫ j) = transfer j ≫ transfer i
  finiteLocallyFree : ∀ n : ℕ, IsFinite (inclusions.obj n).X.hom ∧
    Flat (inclusions.obj n).X.hom ∧ LocallyOfFinitePresentation (inclusions.obj n).X.hom
  multiplication : ∀ {m n : ℕ} (i : m ⟶ n),
    transfer i ≫ inclusions.map i = p ^ (n - m) • (𝟙 (inclusions.obj n))
  shortExact : ∀ m n : ℕ,
    CommGroupScheme.AffineFppfShortExact (inclusions.map (homOfLE (Nat.le_add_left n m)))
      (transfer (homOfLE (Nat.le_add_right m n)))

namespace PDivisibleGroup

variable {R : CommRingCat.{v}} {p : ℕ} [Fact p.Prime]

/-- The same actual levels with the opposite multiplication transitions. -/
def inverseSystem (G : PDivisibleGroup R p) : ℕᵒᵖ ⥤ CommGroupScheme (Spec R) where
  obj n := G.inclusions.obj n.unop
  map i := G.transfer i.unop
  map_id n := G.transfer_id n.unop
  map_comp i j := G.transfer_comp j.unop i.unop

/-- The rank of the actual finite affine coordinate algebra at a base prime. -/
def levelRank (G : PDivisibleGroup R p) (n : ℕ) : PrimeSpectrum R → ℕ :=
  Module.rankAtStalk (R := R) ((algΓ R).obj (G.inclusions.obj n).X).unop

/-- A constant height is measured on the actual coordinate algebras. -/
def HasHeight (G : PDivisibleGroup R p) (h : ℕ) : Prop :=
  ∀ (n : ℕ) (x : PrimeSpectrum R), G.levelRank n x = p ^ (n * h)

end PDivisibleGroup

namespace FormalGroup.ModuleLaw.IsPiDivisible

open GroupScheme.Cartier.FiniteDual

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ} {p : ℕ} [Fact p.Prime]

/-- The p-divisible group of a formal module is given by its actual p-power kernel schemes. -/
def pDivisibleGroup (hM : M.IsPiDivisible (p : O)) : PDivisibleGroup (CommRingCat.of R) p where
  inclusions := hM.torsionSchemeInclusions
  transfer i := hM.torsionSchemeTower.map i.op
  transfer_id n := hM.torsionSchemeTower.map_id (op n)
  transfer_comp i j := hM.torsionSchemeTower.map_comp j.op i.op
  finiteLocallyFree n := by
    let P := hM.torsionKernelModel n
    change IsFinite P.commGroupScheme.X.hom ∧ Flat P.commGroupScheme.X.hom ∧
      LocallyOfFinitePresentation P.commGroupScheme.X.hom
    exact algSpec_finiteLocallyFree (R := CommRingCat.of R) P.coordinateAlgebra
  multiplication i := hM.torsionSchemeTower_comp_inclusion i
  shortExact m n := hM.torsionSchemes_affineFppfShortExact m n

/-- The constant height of a divisible formal law is the height of its actual tower. -/
theorem pDivisibleGroup_hasHeight {h : ℕ} (hM : M.HasPiHeight (p : O) p h) :
    hM.piDivisible.pDivisibleGroup.HasHeight h := by
  intro n x
  let P := hM.piDivisible.torsionKernelModel n
  change Module.rankAtStalk (R := R) (sections (specOver (CommRingCat.of R) P.coordinateAlgebra)) x = _
  have he := congrFun (Module.rankAtStalk_eq_of_equiv
    (sectionsSpec (CommRingCat.of R) P.coordinateAlgebra).symm.toLinearEquiv) x
  exact he.symm.trans ((Hom.hasKernelRank_iff _ P _).mp (hM.scalarPower_rank n) x)

end FormalGroup.ModuleLaw.IsPiDivisible
end Langlands
