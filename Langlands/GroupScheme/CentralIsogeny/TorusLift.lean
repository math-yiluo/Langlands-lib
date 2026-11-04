import Langlands.GroupScheme.CentralIsogeny.PowerLift
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SchematicImageComparison

/-! # Lifting every target torus through a central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A surjective homomorphism between actual field tori is flat, including
inseparable maps and nonsplit tori. -/
theorem IsTorus.flat_of_surjective_hom
    {T S : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) (hS : IsTorus S) (f : T ⟶ S)
    (hf : Surjective f.hom.hom.left) : Flat f.hom.hom.left := by
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  have : IsAffine S.X.left := SplittingAssembly.isAffine_of_isTorus S hS
  have : IsAffineHom T.X.hom := inferInstance
  have : IsAffineHom S.X.hom := inferInstance
  have : Smooth T.X.hom := hT.smooth
  have : Smooth S.X.hom := hS.smooth
  have : ConnectedSpace S.X.left := hS.connectedSpace
  have : GeometricallyIntegral S.X.hom :=
    smoothConnectedAffineGeometry.1 k S inferInstance inferInstance inferInstance
  have : IsLocallyNoetherian S.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian S.X.hom
  have : IsReduced S.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian S.X.hom
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ S.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp _ S.X.hom
  have : Surjective f.hom.hom.left := hf
  exact DominantHomFlat.flat_of_isDominant f

/-- A torus parametrization surjecting onto a closed target subgroup gives a
closed torus lift and a surjective restriction map. -/
theorem exists_subtorus_lift_of_surjective_torusParametrization
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (π : G ⟶ H)
    {D S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : D.toGrp ⟶ G) (b : D.toGrp ⟶ S.toGrp) (i : S.toGrp ⟶ H)
    (hD : IsTorus D.toGrp) (hi : IsClosedSubgroup i)
    (hb : Surjective b.hom.hom.left) (hcomm : a ≫ π = b ≫ i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (f : T.toGrp ⟶ S.toGrp),
      IsTorus T.toGrp ∧ IsClosedSubgroup j ∧ Surjective f.hom.hom.left ∧
        j ≫ π = f ≫ i := by
  have : IsAffine D.toGrp.X.left :=
    SplittingAssembly.isAffine_of_isTorus D.toGrp hD
  have : IsAffineHom D.toGrp.X.hom := inferInstance
  have hT : IsTorus (SchematicImage.image a) := hD.isTorus_schematicImage a
  let T : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image a with comm := hT.isCommMonObj }
  let j : T.toGrp ⟶ G := SchematicImage.inclusion a
  let p : D.toGrp ⟶ T.toGrp := SchematicImage.projection a
  have : IsSchemeTheoreticallyDominant p.hom.hom.left := inferInstance
  have hfac : p ≫ (j ≫ π) = b ≫ i := by
    rw [← Category.assoc, SchematicImage.projection_inclusion, hcomm]
  have hr : SubgroupFunctor.range (p ≫ (j ≫ π)) ≤ SubgroupFunctor.range i := by
    rw [hfac]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ b.hom.hom, Category.assoc _ _ _⟩
  have hr' : SubgroupFunctor.range (j ≫ π) ≤ SubgroupFunctor.range i :=
    (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
      p (j ≫ π) i hi).mp hr
  have : IsClosedImmersion i.hom.hom.left := hi
  let ri : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let f := ri.factorHom (j ≫ π) hr'
  have hfi : f ≫ i = j ≫ π := ri.factorHom_comp _ _
  have hpf : p ≫ f = b := by
    apply ri.hom_ext
    rw [Category.assoc, hfi, hfac]
  have : Surjective (p.hom.hom.left ≫ f.hom.hom.left) := by
    change Surjective (p ≫ f).hom.hom.left
    rw [hpf]
    exact hb
  exact ⟨T, j, f, hT,
    inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion a).hom.hom.left),
    Surjective.of_comp p.hom.hom.left f.hom.hom.left, hfi.symm⟩

/-- Every closed torus in the target of a central isogeny with affine source
lifts to a closed source torus mapping isogenously onto it. -/
theorem IsCentralIsogeny.exists_isogeny_torus_lift
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {π : G ⟶ H} (hπ : IsCentralIsogeny π)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H)
    (hS : IsTorus S.toGrp) (hi : IsClosedSubgroup i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (f : T.toGrp ⟶ S.toGrp),
      IsTorus T.toGrp ∧ IsClosedSubgroup j ∧ IsIsogeny f ∧ j ≫ π = f ≫ i := by
  obtain ⟨N, hN, he⟩ := hπ.exists_pow_eq_one_kernel
  obtain ⟨Φ, hΦ⟩ := hπ.exists_comp_eq_multiplication_comp i he
  have hn : ((2 * N : ℕ) : ℤ) ≠ 0 := by omega
  have hs : Surjective (multiplication S.toGrp (2 * N : ℕ)).hom.hom.left :=
    (hS.flat_and_surjective_multiplication hn).2
  obtain ⟨T, j, f, hT, hj, hf, hcomm⟩ :=
    exists_subtorus_lift_of_surjective_torusParametrization
      π Φ (multiplication S.toGrp (2 * N : ℕ)) i hS hi hs hΦ
  have : IsFinite π.hom.hom.left := hπ.isFinite
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion i.hom.hom.left := hi
  have hc : IsFinite (f.hom.hom.left ≫ i.hom.hom.left) := by
    change IsFinite (f ≫ i).hom.hom.left
    rw [← hcomm]
    change IsFinite (j.hom.hom.left ≫ π.hom.hom.left)
    infer_instance
  exact ⟨T, j, f, hT, hj,
    ⟨IsFinite.of_comp _ i.hom.hom.left, hT.flat_of_surjective_hom hS f hf, hf⟩, hcomm⟩

/-- The universe-general all-target-torus lifting property of central isogenies. -/
def CentralIsogenyTorusLiftStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (π : G ⟶ H), IsCentralIsogeny π →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H),
      IsTorus S.toGrp → IsClosedSubgroup i →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
        (j : T.toGrp ⟶ G) (f : T.toGrp ⟶ S.toGrp),
        IsTorus T.toGrp ∧ IsClosedSubgroup j ∧ IsIsogeny f ∧ j ≫ π = f ≫ i

theorem centralIsogenyTorusLiftStatement : CentralIsogenyTorusLiftStatement.{u} := by
  intro k _ G H _ π hπ S i hS hi
  exact hπ.exists_isogeny_torus_lift S i hS hi

end Langlands.GroupScheme
