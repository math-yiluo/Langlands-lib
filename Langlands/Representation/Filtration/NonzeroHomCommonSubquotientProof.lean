import Langlands.Representation.Filtration.NonzeroHomCommonSubquotientStatement

/-! The Artinian image argument, with actual subquotients in independent universes. -/

noncomputable section

namespace Langlands

universe uK uG uV uW

/-- A nonzero intertwiner into an Artinian representation has a common
irreducible actual subquotient with its source. -/
theorem nonzeroHomCommonSubquotient :
    NonzeroHomCommonSubquotientTheorem.{uK, uG, uV, uW} := by
  intro k _ G _ _ A B hArt hHom
  let := hArt
  obtain ⟨f, hf⟩ := hHom
  let fg := Representation.IntertwiningMap.equivLinearMapAsModule
    A.representation B.representation f
  have hfg : fg ≠ 0 := by
    exact (LinearEquiv.map_ne_zero_iff _).mpr hf
  have hrange : fg.range ≠ ⊥ := by
    exact fun h => hfg (LinearMap.range_eq_bot.mp h)
  obtain ⟨N, hN, hNrange⟩ := (eq_bot_or_exists_atom_le fg.range).resolve_left hrange
  let S' : Subrepresentation B.representation := Subrepresentation.ofSubmodule' N
  let S : Subrepresentation A.representation :=
    Subrepresentation.ofSubmodule' (N.comap fg)
  let q : (SmoothRep.subrepresentation A S).representation.IntertwiningMap
      (SmoothRep.subrepresentation B S').representation :=
    { toLinearMap :=
        { toFun := fun v => ⟨f v.val, v.property⟩
          map_add' := fun _ _ => Subtype.ext (map_add f _ _)
          map_smul' := fun _ _ => Subtype.ext (map_smul f _ _) }
      isIntertwining' := fun g => by
        ext v
        exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ f g v.val) }
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w, hw⟩ := hNrange v.property
    refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
    change fg w ∈ N
    rw [hw]
    exact v.property
  let e : (SmoothRep.subquotient A S q.ker).representation.Equiv
      (SmoothRep.subrepresentation B S').representation :=
    Representation.Equiv.mk (q.toLinearMap.quotKerEquivOfSurjective hq) fun g => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ q g v
  let j : (SmoothRep.subrepresentation B S').representation.asModule →ₗ[MonoidAlgebra k G] N :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.hom (SmoothRep.subtype B S'))).codRestrict N (fun v => v.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
  have hsimple : IsSimpleModule (MonoidAlgebra k G)
      (SmoothRep.subrepresentation B S').representation.asModule :=
    (j.isSimpleModule_iff_of_bijective hj).mpr (isSimpleModule_iff_isAtom.mpr hN)
  let i := Representation.IntertwiningMap.id (SmoothRep.subrepresentation B S').representation
  let e' : (SmoothRep.subquotient B S' i.ker).representation.Equiv
      (SmoothRep.subrepresentation B S').representation :=
    Representation.Equiv.mk (i.toLinearMap.quotKerEquivOfSurjective Function.surjective_id)
      fun g => by
        apply Submodule.linearMap_qext
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ i g v
  refine ⟨S, q.ker, S', i.ker, ?_, ⟨e.trans e'.symm⟩⟩
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  exact ((Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap).isSimpleModule_iff_of_bijective e.bijective).mpr hsimple

end Langlands
