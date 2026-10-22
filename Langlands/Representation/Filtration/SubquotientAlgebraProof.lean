import Langlands.Representation.Filtration.SubquotientAlgebraStatement

namespace Langlands

open CategoryTheory

universe uK uG uV

theorem smoothSubquotientTransitivity :
    SmoothSubquotientTransitivityTheorem.{uK, uG, uV} := by
  intro k _ G _ _ A B C hCB hBA
  obtain ⟨S, Q, ⟨e⟩⟩ := hCB
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hBA
  let qg := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom q)
  let P : Subrepresentation X.representation :=
    Subrepresentation.ofSubmodule' (S.asSubmodule.comap qg)
  let r : (SmoothRep.subrepresentation X P).representation.IntertwiningMap
      (SmoothRep.subrepresentation B S).representation :=
    { toLinearMap :=
        { toFun := fun v => ⟨SmoothRep.hom q v.val, v.property⟩
          map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
          map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
      isIntertwining' := fun g => by
        ext v
        exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom q) g v.val) }
  have hr : Function.Surjective r := by
    intro v
    obtain ⟨x, hx⟩ := hq v.val
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change SmoothRep.hom q x ∈ S
    rw [hx]
    exact v.property
  refine SmoothRep.isSubquotient_iff_exists.mpr
    ⟨SmoothRep.subrepresentation X P, SmoothRep.subtype X P ≫ i,
      SmoothRep.ofHom r ≫ SmoothRep.mkQ (SmoothRep.subrepresentation B S) Q ≫ e.inv,
      ?_, ?_⟩
  · exact hi.comp (SmoothRep.subtype_injective X P)
  · exact (SmoothRep.hom_hom_surjective e.symm).comp
      ((SmoothRep.mkQ_surjective _ Q).comp hr)

theorem smoothSubquotientArtinian :
    SmoothSubquotientArtinianTheorem.{uK, uG, uV} := by
  intro k _ G _ _ A B hArt hB
  let := hArt
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hB
  let ig := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom i)
  let qg := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom q)
  let : IsArtinian (MonoidAlgebra k G) X.representation.asModule :=
    isArtinian_of_injective ig hi
  exact isArtinian_of_surjective _ qg hq

theorem smoothSubquotientAlgebra :
    SmoothSubquotientAlgebraTheorem.{uK, uG, uV} :=
  ⟨smoothSubquotientTransitivity, smoothSubquotientArtinian⟩

end Langlands
