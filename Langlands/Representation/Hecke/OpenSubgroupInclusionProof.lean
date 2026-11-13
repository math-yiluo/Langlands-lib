import Langlands.Representation.Hecke.OpenSubgroupPseudo

noncomputable section

open MeasureTheory

namespace Langlands.Hecke.Homomorphism

universe uG v

theorem openSubgroupHeckeInclusion :
    OpenSubgroupHeckeInclusionStatement.{uG, v} := by
  intro G _ _ _ _ _ _ _ μG _ H hH
  let : LocallyCompactSpace H :=
    (Subgroup.isClosed_of_isOpen H hH).locallyCompactSpace
  intro μH _
  refine ⟨open_relativeModularCharacter H hH, open_relativeModular H hH,
    ⟨OpenSubgroup.pseudoFIsoF H hH μG μH⟩, ?_⟩
  intro hμ
  refine ⟨openHeckeInclusion H hH μG μH, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h
    change openHeckeLinear H hH μG μH a (h : G) = a h
    rw [openHeckeLinear_apply_subtype, openDensity_eq_one H hH μG μH hμ, one_mul]
  · intro a x hx
    exact openHeckeLinear_apply_not_mem H hH μG μH a hx
  · intro T hT
    exact openHeckeLinear_surj_supported H hH μG μH T hT
  · exact open_leftModule_eq H hH μG μH
  · exact open_rightModule_eq H hH μG μH

end Langlands.Hecke.Homomorphism
