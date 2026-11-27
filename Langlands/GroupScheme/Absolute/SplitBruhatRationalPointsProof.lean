import Langlands.GroupScheme.Absolute.SplitBruhatRationalPointsStatement
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting

/-! # Split Bruhat decomposition for the points of a Borel pair -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The rational Bruhat bijection for a regular cocharacter gives the
double-coset bijection for the Borel subgroup it represents. -/
theorem splitBruhatRationalPoints : SplitBruhatRationalPointsStatement.{u} := by
  intro k _ G B T b t hG hPair hT
  let := hG.isAffineHom
  obtain ⟨hB, ht, f, hf⟩ := hPair
  obtain ⟨ν, hν, hrep⟩ := (regularCocharacterBorel k G hG T t hT ht).2.2 B b f hB hf
  have hbr := rationalBruhat k G hG T t (ht.isMaximalSplitTorus hT) ν hν
  have hbij := (hasRationalBruhatDecomposition_iff_bijective t ν).mp hbr
  unfold BorelTorusBruhatRationalPoints
  dsimp
  rw [hrep.2]
  exact ⟨Equiv.ofBijective (relativeWeylToDoubleCosets t ν) hbij, fun _ => rfl⟩

/-- Every Borel pair over a separably closed field has the Bruhat
double-coset bijection, since its maximal torus is split. -/
theorem IsBorelPair.bruhatRationalPoints_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : B ⟶ G} {t : T.toGrp ⟶ G}
    (hPair : IsBorelPair b t) (hG : IsConnectedReductive G) :
    BorelTorusBruhatRationalPoints b t :=
  splitBruhatRationalPoints k G B T b t hG hPair (toriAreSplit_of_isSepClosed k _ hPair.2.1.1)

end Langlands.GroupScheme
