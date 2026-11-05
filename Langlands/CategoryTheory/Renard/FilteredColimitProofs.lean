import Langlands.CategoryTheory.Renard.FilteredColimitStatements

/-!
# Renard A.IV.2: the concrete directed quotient is a colimit

The actual quotient lift factors compatible families uniquely. It supplies the
categorical colimit witness for the lifted diagram. The defining quotient
relation gives eventual zero, and the empty diagram uses its singleton cocone.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.FilteredColimit

universe uI uG uH

/-- The published quotient lift factors the original components uniquely. -/
theorem compatibleFamilyLiftStatement :
    CompatibleFamilyLiftStatement.{uI, uG, uH} := by
  intro I _ _ _ G _ f _ H _ g hg
  constructor
  · intro i
    ext x
    exact lift_classOf G f g hg i x
  · intro l hl
    ext z
    obtain ⟨i, x, rfl⟩ := exists_classOf G f z
    calc
      l (classOf G f i x) = g i x := DFunLike.congr_fun (hl i) x
      _ = lift G f g hg (classOf G f i x) := (lift_classOf G f g hg i x).symm

/-- Raising the components of a cocone gives the compatible family for its descent. -/
theorem quotientColimitStatement : QuotientColimitStatement.{uI, uG} := by
  intro I _ _ _ G _ f _
  let g (s : Cocone (diagram G f)) (i : I) : G i →+ s.pt :=
    (s.ι.app i).hom.comp
      (AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i).symm.toAddMonoidHom
  have hg (s : Cocone (diagram G f)) (i j : I) (h : i ≤ j) (x : G i) :
      g s j (f i j h x) = g s i x := by
    have hn := congrArg (fun a => a (ULift.up x)) (s.w (homOfLE h))
    exact hn
  refine ⟨{
    desc := fun s => AddCommGrpCat.ofHom (lift G f (g s) (hg s))
    fac := ?_
    uniq := ?_ }⟩
  · intro s i
    apply AddCommGrpCat.ext
    intro x
    change lift G f (g s) (hg s) (classOf G f i x.down) = (s.ι.app i) x
    rw [lift_classOf]
    rfl
  · intro s m hm
    apply AddCommGrpCat.hom_ext
    apply (compatibleFamilyLiftStatement I G f s.pt (g s) (hg s)).2
    intro i
    ext x
    exact congrArg (fun a => a (ULift.up x)) (hm i)

/-- Equality with the zero representative gives a forward stage where the element is zero. -/
theorem eventualZeroStatement : EventualZeroStatement.{uI, uG} := by
  intro I _ _ _ G _ f _ i x hx
  rw [of_apply, zero_eq_classOf G f i] at hx
  obtain ⟨j, hij, _, hj⟩ := (classOf_eq_iff G f i i x 0).1 hx
  exact ⟨j, hij, by simpa only [map_zero] using hj⟩

/-- The converse uses transition compatibility and preservation of zero. -/
theorem eventualZeroIffStatement : EventualZeroIffStatement.{uI, uG} := by
  intro I _ _ _ G _ f _ i x
  constructor
  · exact eventualZeroStatement I G f i x
  · rintro ⟨j, hij, hx⟩
    calc
      of G f i x = of G f j (f i j hij x) :=
        (DFunLike.congr_fun (of_comp G f i j hij) x).symm
      _ = 0 := by rw [hx, map_zero]

/-- The singleton vertex admits exactly one homomorphism to every abelian group. -/
theorem emptyColimitStatement : EmptyColimitStatement.{uI, uG} := by
  intro I _ _ G _ f _
  refine ⟨{
    desc := fun s => AddCommGrpCat.ofHom (0 : PUnit →+ s.pt)
    fac := ?_
    uniq := ?_ }⟩
  · intro s i
    exact isEmptyElim i
  · intro s m _
    dsimp only [emptyCocone] at m ⊢
    apply AddCommGrpCat.hom_ext
    ext x
    change m.hom x = 0
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact m.hom.map_zero

/-- The five published concrete quotient conclusions, with independent universes. -/
theorem filteredColimitStatements : FilteredColimitStatements.{uI, uG, uH} :=
  ⟨quotientColimitStatement, compatibleFamilyLiftStatement,
    eventualZeroStatement, eventualZeroIffStatement, emptyColimitStatement⟩

end Langlands.Renard.FilteredColimit
