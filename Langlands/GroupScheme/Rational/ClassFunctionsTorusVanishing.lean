import Langlands.GroupScheme.Rational.ClassFunctionsAlgClosedStronglyRegularFibres
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Absolute.BorelFieldExtensionMaximality
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints

/-! # Class functions vanishing on a maximal torus over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

variable {k : Type u} [Field k]

local notation "U₀" => 𝟙_ (Over (Spec (CommRingCat.of k)))

/-- A regular class function `f` vanishes at the torus points along `jT`: its value at the
image `s ≫ jT` of every affine `k`-point `s` of `T` is zero. -/
def VanishesOnTorusPoints {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (jT : T.toGrp ⟶ G) (f : algebra G) : Prop :=
  ∀ s : Lie.AffinePoints T.toGrp k, Lie.pointCoordinates G (s ≫ jT.hom.hom) f.val = 0

open AlgClosedFibres in
/-- Given that every rational point lies in a Borel subgroup, every rational point of a
connected reductive group over an algebraically closed field has the quotient image of a
rational point of any given maximal torus. -/
theorem exists_torusPoint_rho_eq (hP1 : BorelPointContainmentStatement.{u}) [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {jT : T.toGrp ⟶ G}
    (hjT : IsMaximalTorus jT) (y : U₀ ⟶ G.X) :
    ∃ t : U₀ ⟶ T.X, y ≫ rho G = (t ≫ jT.hom.hom) ≫ rho G := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  -- `y` lies in a Borel subgroup, which contains a split maximal torus
  obtain ⟨B, i, b, hB, hb⟩ := hP1 k G y
  obtain ⟨T₁, jT₁, -, hjT₁, f₁, hf₁⟩ := borelMaximalTorus k G B i hB
  have hTs : IsSplitTorus T₁.toGrp :=
    SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
      CoalgebraDescent.separablyClosedGroupLikeSpanning T₁.toGrp hjT₁.1
  obtain ⟨ν, hν, hrep⟩ := (regularCocharacterBorel k G hG T₁ jT₁ hTs hjT₁).2.2 B i f₁ hB hf₁
  let χ := CommGroupScheme.groupHom ν ≫ jT₁
  have hy : y ∈ (Dynamic.parabolic χ).carrier (𝟙_ _) := by
    rw [← hrep.2]
    exact ⟨b, hb⟩
  have hZ := centralizer_comp_eq_range_of_isRegular hG hTs jT₁ hjT₁ ν hν
  -- the limit of `y` lies in `T₁` and has the quotient image of `y`
  let t := Dynamic.limit χ ⟨y, hy⟩
  have ht : t ∈ (Dynamic.centralizer χ).carrier (𝟙_ _) := Dynamic.limit_mem_centralizer χ _
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : U₀ ⟶ T₁.X, t₀ ≫ jT₁.hom.hom = t := by
    have h := ht
    rw [hZ] at h
    exact h
  -- the point `t₀` of `T₁` is conjugate to a point of `T`
  obtain ⟨g, t', hg⟩ := exists_conj_eq_comp_of_isTorus hjT jT₁ hjT₁.1 hjT₁.2.1 t₀
  refine ⟨t', ?_⟩
  rw [← hg, rho_conjugation, ht₀]
  exact rho_limit G χ ⟨y, hy⟩

/-- **Class functions are detected on a maximal torus.** Given that every rational point lies
in a Borel subgroup, a regular class function on a connected reductive group over an
algebraically closed field vanishing at every rational point of a maximal torus is zero. -/
theorem eq_zero_of_vanishesOnTorusPoints (hP1 : BorelPointContainmentStatement.{u})
    [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {jT : T.toGrp ⟶ G}
    (hjT : IsMaximalTorus jT) (f : algebra G) (hf : VanishesOnTorusPoints jT f) :
    f = 0 := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let e : (algSpec (CommRingCat.of k)).obj (Opposite.op (CommAlgCat.of (CommRingCat.of k) k)) ≅
      U₀ := Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k
  -- `f` vanishes at every rational point
  have hval : ∀ x : Lie.AffinePoints G k, Lie.pointCoordinates G x f.val = 0 := by
    intro x
    obtain ⟨t', ht'⟩ := exists_torusPoint_rho_eq hP1 hG hjT (e.inv ≫ x)
    have h := congrArg (fun z => e.hom ≫ z) ht'
    simp only [← Category.assoc, e.hom_inv_id, Category.id_comp] at h
    rw [evaluation_eq_of_rho_eq G x ((e.hom ≫ t') ≫ jT.hom.hom) h f]
    exact hf (e.hom ≫ t')
  -- the Nullstellensatz on the coordinate domain
  have := CharacterLatticeProof.isDomain_coord G
  have : Algebra.FiniteType k (Coord G) := Lie.coordinateAlgebraFiniteType G
  apply Subtype.ext
  by_contra hne
  obtain ⟨φ, hφ⟩ := BorelFieldExtension.exists_algHom_ne_zero (K := k) (R := Coord G) hne
  apply hφ
  have h := hval ((Lie.pointCoordinates G).symm φ)
  rwa [Equiv.apply_symm_apply] at h

end Langlands.GroupScheme.ClassFunctions
