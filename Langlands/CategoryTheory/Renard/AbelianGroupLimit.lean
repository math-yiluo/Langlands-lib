import Langlands.CategoryTheory.Renard.AbelianGroupLimitStatements

/-!
# Renard A.IV.2: concrete products and direct sums of abelian groups

Direct proofs of the four published statements. The universal maps lower or
raise individual coordinates through `AddEquiv.ulift`, leaving the product
and direct-sum vertices unchanged.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.AbelianGroupLimit

universe uI uG

/-- The coordinatewise map supplies the actual Cartesian-product limit. -/
theorem cartesianProductStatement : CartesianProductStatement.{uI, uG} := by
  intro I G
  refine ⟨Fan.IsLimit.mk _ (fun s => AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun i =>
      (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).toAddMonoidHom.comp
        (s.proj i).hom)) ?_ ?_⟩
  · intro s i
    apply AddCommGrpCat.ext
    intro x
    apply ULift.ext
    rfl
  · intro s m hm
    apply AddCommGrpCat.ext
    intro x
    funext i
    exact congrArg (fun f => (f x).down) (hm i)

/-- Evaluation on single-coordinate generators supplies the direct-sum colimit. -/
theorem directSumCoproductStatement : DirectSumCoproductStatement.{uI, uG} := by
  classical
  intro I G
  refine ⟨Cofan.IsColimit.mk _ (fun s => AddCommGrpCat.ofHom
    (DirectSum.toAddMonoid fun i =>
      (s.inj i).hom.comp
        (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).symm.toAddMonoidHom)) ?_ ?_⟩
  · intro s i
    apply AddCommGrpCat.ext
    intro x
    simp
  · intro s m hm
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro i x
    have h := congrArg (fun f => f (ULift.up x)) (hm i)
    simp only [AddCommGrpCat.hom_ofHom, DirectSum.toAddMonoid_of]
    change m.hom (DirectSum.of (fun i => G i) i x) = (s.inj i).hom (ULift.up x)
    change m.hom (DirectSum.of (fun i => G i) i x) = (s.inj i).hom (ULift.up x) at h
    exact h

/-- The coordinate embedding has exactly the finitely supported families as image. -/
theorem finiteSupportComparisonStatement : FiniteSupportComparisonStatement.{uI, uG} := by
  classical
  intro I G
  refine ⟨DFunLike.coe_injective, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact DFinsupp.finite_support y
    · intro hx
      refine ⟨DFinsupp.mk (β := fun i => G i) hx.toFinset (fun i => x i), ?_⟩
      funext i
      change (DFinsupp.mk (β := fun i => G i) hx.toFinset (fun i => x i)) i = x i
      rw [DFinsupp.mk_apply]
      by_cases hi : x i = 0 <;> simp_all
  · intro i
    apply AddMonoidHom.ext
    intro x
    exact DFinsupp.single_eq_pi_single

/-- A finite Cartesian product is a coproduct via the finite direct-sum equivalence. -/
theorem finiteProductCoproductStatement : FiniteProductCoproductStatement.{uI, uG} := by
  classical
  intro I _ G
  let := Fintype.ofFinite I
  let e := DirectSum.addEquivProd (fun i => G i)
  refine ⟨Cofan.IsColimit.mk _ (fun s => AddCommGrpCat.ofHom
    ((DirectSum.toAddMonoid fun i =>
      (s.inj i).hom.comp
        (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).symm.toAddMonoidHom).comp
      e.symm.toAddMonoidHom)) ?_ ?_⟩
  · intro s i
    apply AddCommGrpCat.ext
    intro x
    change DirectSum.toAddMonoid
      (fun i => (s.inj i).hom.comp
        (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).symm.toAddMonoidHom)
      (e.symm (Pi.single i x.down)) = (s.inj i) x
    have he : e.symm (Pi.single i x.down) = DirectSum.of (fun i => G i) i x.down :=
      DFinsupp.equivFunOnFintype_symm_single (β := fun i => G i) i x.down
    rw [he, DirectSum.toAddMonoid_of]
    rfl
  · intro s m hm
    apply AddCommGrpCat.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    have h : m.hom.comp e.toAddMonoidHom =
        DirectSum.toAddMonoid (fun i =>
          (s.inj i).hom.comp
            (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).symm.toAddMonoidHom) := by
      apply DirectSum.addHom_ext
      intro i z
      have h := congrArg (fun f => f (ULift.up z)) (hm i)
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
      change m.hom (Pi.single i z) = (s.inj i).hom (ULift.up z)
      change m.hom (Pi.single i z) = (s.inj i).hom (ULift.up z) at h
      exact h
    simpa using DFunLike.congr_fun h y

/-- Renard's product/direct-sum example, at independent index and group universes. -/
theorem abelianGroupLimitStatements : AbelianGroupLimitStatements.{uI, uG} :=
  ⟨cartesianProductStatement, directSumCoproductStatement,
    finiteSupportComparisonStatement, finiteProductCoproductStatement⟩

end Langlands.Renard.AbelianGroupLimit
