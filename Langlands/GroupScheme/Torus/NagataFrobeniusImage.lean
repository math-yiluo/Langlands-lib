import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.Adjoint.SecondCenterReductive
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Langlands.GroupScheme.Rational.ClosedImmersionPullbackProof

/-! # Affine Frobenius image quotients and coordinate powers -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

local instance (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n] :
    IsAffineHom (GeneralLinear.groupScheme n (CommRingCat.of k)).X.hom :=
  GeneralLinear.isAffineHom_groupScheme n (CommRingCat.of k)

namespace GeneralLinear

variable (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [ExpChar k p]
  (n : Type) [Fintype n] [DecidableEq n]

/-- Pullback along the matrix Frobenius takes values in the characteristic powers
of the explicit coordinate ring over an algebraically closed field. -/
theorem exists_pow_frobeniusCoordinates (a : CoordinateRing n k) :
    ∃ b : CoordinateRing n k, frobeniusCoordinates k p n a = b ^ p := by
  have hX (v : Coordinate n) :
      frobeniusCoordinates k p n (quotient n k (MvPolynomial.X v)) =
        quotient n k (MvPolynomial.X v) ^ p := by
    cases v with
    | entry i j => exact frobeniusCoordinates_entry k p n i j
    | inverseEntry i j => exact frobeniusCoordinates_inverseEntry k p n i j
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
  change ∃ b, frobeniusCoordinates k p n (quotient n k F) = b ^ p
  induction F using MvPolynomial.induction_on with
  | C c =>
      obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero (expChar_ne_zero k p))
      refine ⟨algebraMap k (CoordinateRing n k) d, ?_⟩
      rw [← map_pow, hd]
      change frobeniusCoordinates k p n (algebraMap k (CoordinateRing n k) c) = _
      exact (frobeniusCoordinates k p n).commutes c
  | add F F' hF hF' =>
      obtain ⟨b, hb⟩ := hF
      obtain ⟨c, hc⟩ := hF'
      refine ⟨b + c, ?_⟩
      rw [map_add, map_add, hb, hc]
      exact ((algebraFrobenius k p (CoordinateRing n k)).map_add b c).symm
  | mul_X F v hF =>
      obtain ⟨b, hb⟩ := hF
      refine ⟨b * quotient n k (MvPolynomial.X v), ?_⟩
      rw [map_mul, map_mul, hb, hX v, mul_pow]

/-- Evaluating the coordinates of a Frobenius image point yields characteristic
powers in the test algebra, in the actual affine coordinate presentation. -/
theorem exists_pow_pointCoordinates_frobeniusHom
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : (groupScheme n (CommRingCat.of k)).affinePoints A)
    (a : CharacterUnits.Coord (groupScheme n (CommRingCat.of k))) :
    ∃ b : A, Lie.pointCoordinates (groupScheme n (CommRingCat.of k))
      (x ≫ (frobeniusHom k p n).hom.hom) a = b ^ p := by
  let R := CommRingCat.of k
  let H := groupScheme n R
  let φ : CoordinateRing n k →ₐ[k] A := classify (affinePointsEquiv n R A x)
  let g : H.affinePoints (coordinateAlgebra n R) := 𝟙 H.X
  let f : coordinateAlgebra n R ⟶ A := CommAlgCat.ofHom φ
  let F : coordinateAlgebra n R ⟶ coordinateAlgebra n R :=
    CommAlgCat.ofHom (frobeniusCoordinates k p n)
  have hx : (algSpec R).map f.op = x :=
    (affinePointsEquiv_symm_apply (n := n) (R := R) A ((affinePointsEquiv n R A) x)).symm.trans
      ((affinePointsEquiv n R A).symm_apply_apply x)
  have hf : (frobeniusHom k p n).hom.hom = (algSpec R).map F.op := by
    apply Over.OverMorphism.ext
    exact frobeniusHom_hom k p n
  have he : x ≫ (frobeniusHom k p n).hom.hom =
      Lie.affineMap H (φ.comp (frobeniusCoordinates k p n)) g := by
    calc
      _ = (algSpec R).map f.op ≫ (algSpec R).map F.op := by rw [hx, hf]
      _ = (algSpec R).map (F ≫ f).op := by rw [op_comp, Functor.map_comp]
      _ = _ := (Category.comp_id ((algSpec R).map (F ≫ f).op)).symm
  rw [he, Lie.pointCoordinates_naturality, AlgHom.comp_apply, AlgHom.comp_apply]
  obtain ⟨b, hb⟩ := exists_pow_frobeniusCoordinates k p n (Lie.pointCoordinates H g a)
  exact ⟨φ b, by rw [hb, map_pow]⟩

end GeneralLinear

/-- The actual image of a characteristic-power matrix representation is an
fppf quotient by its scheme kernel. The quotient pullback takes values in
characteristic powers, including on nonreduced source groups. -/
def FrobeniusImageQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [ExpChar k p]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
    ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ I)
      (i : I ⟶ GeneralLinear.groupScheme n (CommRingCat.of k)),
      LocallyOfFiniteType I.X.hom ∧ ∃ (_ : IsAffineHom I.X.hom),
        IsClosedSubgroup i ∧ q ≫ i = ρ.frobeniusPower p 1 ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι (ρ.frobeniusPower p 1))) q ∧
        IsSchemeTheoreticallyDominant q.hom.hom.left ∧
        ∀ a : CharacterUnits.Coord I,
          ∃ b : CharacterUnits.Coord G, CoordinateWeights.pullback q.hom.hom a = b ^ p

/-- The fppf homomorphism image theorem applied to matrix Frobenius, with its
additional coordinate power property. -/
theorem frobeniusImageQuotient : FrobeniusImageQuotientStatement.{u} := by
  intro k _ _ p _ G _ _ n _ _ ρ
  let H := GeneralLinear.groupScheme n (CommRingCat.of k)
  let : IsAffineHom H.X.hom := GeneralLinear.isAffineHom_groupScheme n (CommRingCat.of k)
  let : Smooth H.X.hom := GeneralLinear.smoothStatement n (CommRingCat.of k)
  obtain ⟨I, q, i, hIft, hIa, hi, hqi, hq⟩ := affineHomImage k G H (ρ.frobeniusPower p 1)
  let : IsAffineHom I.X.hom := hIa
  let : IsAffine I.X.left := isAffine_of_isAffineHom I.X.hom
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
  let : Epi q.hom.hom := Over.epi_of_epi_left _
  refine ⟨I, q, i, hIft, hIa, hi, hqi, hq, SecondCenter.isSchemeTheoreticallyDominant_of_epi _, ?_⟩
  intro a
  have hsurj : Function.Surjective (CoordinateWeights.pullback i.hom.hom) :=
    PointedCoordinateWeights.pullback_surjective_of_isClosedImmersion i.hom.hom hi
  obtain ⟨c, rfl⟩ := hsurj a
  rw [← AlgHom.comp_apply, ← CoordinateWeights.pullback_comp, ← Grp.comp_hom_hom, hqi]
  change ∃ b, CoordinateWeights.pullback (ρ ≫ GeneralLinear.frobeniusHom k p n).hom.hom c = b ^ p
  rw [Grp.comp_hom_hom]
  unfold CoordinateWeights.pullback
  rw [← Category.assoc]
  exact GeneralLinear.exists_pow_pointCoordinates_frobeniusHom k p n _ _ c

end Langlands.GroupScheme
