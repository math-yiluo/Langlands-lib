import Langlands.GroupScheme.Rational.GeneralLinearSolvableRadicalStatement
import Langlands.GroupScheme.Rational.NormalSolvableCentrality
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.Derived.GeneralLinearCenter
import Langlands.GroupScheme.Reductive.GeneralLinearIsConnectedReductiveProof
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Torus.Geometry

/-! # Proof of the solvable radical of `GL_n` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open TorusExistence

private theorem solvableRadical_of_torusCenter
    {k : Type u} [Field k] {Z G : GroupScheme (Spec (CommRingCat.of k))}
    {z : Z ⟶ G} (hG : IsConnectedReductive G) (hZ : IsTorus Z)
    (hz : IsSchemeTheoreticCenter z) : IsSolvableRadical z := by
  let : IsClosedImmersion z.hom.hom.left := hz.1
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  let C := hz.isCentral.commGroupScheme
  refine ⟨hz.1, hZ.smooth, hZ.connectedSpace,
    isSolvableGroupScheme_of_isCommMonObj C.toGrp, hz.isCentral.range_isNormal, ?_⟩
  intro H i hi hsm hcon hsol hn
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth H.X.hom := hsm
  let : ConnectedSpace H.X.left := hcon
  rw [hz.2]
  rintro T _ ⟨x, rfl⟩
  exact hsol.isCentral_of_normal_of_isConnectedReductive_field hG i hi hn T x

private theorem geometricSolvableRadical_of_torusCenter
    {k : Type u} [Field k] {Z G : GroupScheme (Spec (CommRingCat.of k))}
    {z : Z ⟶ G} (hG : IsConnectedReductive G) (hZ : IsTorus Z)
    (hz : IsSchemeTheoreticCenter z) : IsGeometricSolvableRadical z :=
  ⟨solvableRadical_of_torusCenter hG hZ hz,
    solvableRadical_of_torusCenter hG.baseChange_toAlgebraicClosure (IsTorus.baseChange hZ)
      (schemeTheoreticCenterBaseChangeStatement k (AlgebraicClosure k) G Z z hG hz)⟩

/-- The scalar torus in positive rank and identity torus in rank zero represent
the geometric solvable radicals of the corresponding general linear groups. -/
theorem generalLinearSolvableRadical : GeneralLinearSolvableRadicalStatement.{u} := by
  intro k _
  constructor
  · intro n
    apply geometricSolvableRadical_of_torusCenter
      (GeneralLinear.isConnectedReductiveStatement k (Fin (n + 1))) isSplitTorus_gm.isTorus
    exact ⟨GeneralLinear.isClosedSubgroup_scalarTorus _ _,
      GeneralLinear.range_scalarTorus_eq_center _ _⟩
  · let G := GeneralLinear.groupScheme (Fin 0) (CommRingCat.of k)
    have hG : IsConnectedReductive G := GeneralLinear.isConnectedReductiveStatement k (Fin 0)
    let : IsAffineHom G.X.hom := hG.isAffineHom
    apply geometricSolvableRadical_of_torusCenter hG (isTorus_trivialTorus k)
    refine ⟨isClosedSubgroup_trivialTorusHom G, ?_⟩
    ext T x
    have hx : x = 1 := by
      apply (GeneralLinear.pointsEquiv (Fin 0) (CommRingCat.of k) T).injective
      apply Units.ext
      ext i
      exact Fin.elim0 i
    subst x
    exact ⟨fun _ => Subgroup.one_mem _, fun _ => Subgroup.one_mem _⟩

end Langlands.GroupScheme
