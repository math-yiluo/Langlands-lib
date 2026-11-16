import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalGluing
import Langlands.GroupScheme.RelativeLevi.DynamicRadicalIdentification
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.DynamicProof
import Langlands.GroupScheme.RelativeLevi.BaseChange
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange
import Langlands.GroupScheme.RelativeLevi.ModuliFunctorConstruction

/-! # Arbitrary base change of radicals and Levi subgroups in relative parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- A relative radical in an actual dynamic parabolic survives arbitrary
base change, by identifying its ambient image with the dynamic unipotent. -/
theorem radical_baseChange_of_dynamic_parabolic
    {S T : Scheme.{u}} {G P U : GroupScheme S} {i : P ⟶ G} {r : U ⟶ P}
    (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy i)
    (hr : IsRelativeUnipotentRadical r) (b : T ⟶ S) :
    IsRelativeUnipotentRadical ((baseChange b).map r) := by
  have hG' := hG.baseChange b
  let : Smooth ((baseChange b).obj G).X.hom := hG'.smooth
  let : IsAffineHom ((baseChange b).obj G).X.hom := hG'.isAffineHom
  have hP' := hP.baseChange b
  rw [← Dynamic.parabolic_baseChange] at hP'
  have hU' :=
    (isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi hG χ hP r hr).baseChange b
  rw [← Dynamic.unipotent_baseChange, Functor.map_comp] at hU'
  obtain ⟨Z, iZ, _, _, hZ⟩ :=
    (dynamicBaseRepresentability T ((baseChange b).obj G)
      (Dynamic.baseChangeCocharacter b χ)).2.2
  exact (dynamicRelativeLevi T ((baseChange b).obj G) ((baseChange b).obj P)
    ((baseChange b).obj U) Z (Dynamic.baseChangeCocharacter b χ)
    ((baseChange b).map i) ((baseChange b).map r ≫ (baseChange b).map i) iZ
    hG' hP' hU' hZ).2.1 _ rfl

private theorem radical_square_iff
    {S S' T T' : Scheme.{u}} (a : T ⟶ S) (b : S' ⟶ S)
    (c : T' ⟶ T) (d : T' ⟶ S') (h : c ≫ a = d ≫ b)
    {U P : GroupScheme S} (r : U ⟶ P) :
    IsRelativeUnipotentRadical ((baseChange c).map ((baseChange a).map r)) ↔
      IsRelativeUnipotentRadical ((baseChange d).map ((baseChange b).map r)) := by
  let e :
      baseChange a ⋙ baseChange c ≅ baseChange b ⋙ baseChange d :=
    (Functor.mapGrpNatIso (Over.pullbackComp c a) ≪≫ Functor.mapGrpCompIso).symm ≪≫
      eqToIso (congrArg (fun f => baseChange f) h) ≪≫
      Functor.mapGrpNatIso (Over.pullbackComp d b) ≪≫ Functor.mapGrpCompIso
  have hn :
      (baseChange c).map ((baseChange a).map r) ≫ (e.app P).hom =
        (e.app U).hom ≫ (baseChange d).map ((baseChange b).map r) :=
    e.hom.naturality r
  constructor
  · intro hr
    have ht := (hr.comp_iso (e.app P)).precomp_iso (e.app U).symm
    simpa only [Iso.symm_hom, hn, Iso.inv_hom_id_assoc] using ht
  · intro hr
    have ht := (hr.precomp_iso (e.app U)).comp_iso (e.app P).symm
    simpa only [Iso.symm_hom, ← Category.assoc, ← hn, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using ht

end RelativeLevi

variable {S T : Scheme.{u}} {G P U L : GroupScheme S}
    {i : P ⟶ G} {r : U ⟶ P} {l : L ⟶ P}

/-- In a parabolic of a reductive group, the supplied relative radical
is preserved by every base change. -/
theorem IsRelativeUnipotentRadical.baseChange_parabolic
    (hr : IsRelativeUnipotentRadical r) (hi : IsRelativeParabolicSubgroup i)
    (hG : IsReductive G) (b : T ⟶ S) :
    IsRelativeUnipotentRadical ((baseChange b).map r) := by
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : IsAffineHom ((baseChange b).obj P).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom b)
    exact MorphismProperty.pullback_snd _ _ hi.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := relativeParabolicEtaleLocalDynamic S G P i hG hi
  have hlocal (j : 𝒰.I₀) : IsRelativeUnipotentRadical
      ((baseChange ((𝒰.pullback₁ b).f j)).map ((baseChange b).map r)) := by
    let : Etale (𝒰.f j) := 𝒰.map_prop j
    obtain ⟨χ, hχ⟩ := h𝒰 j
    apply (RelativeLevi.radical_square_iff (𝒰.f j) b
      (𝒰.pullbackHom b j) ((𝒰.pullback₁ b).f j) (𝒰.pullbackHom_map b j) r).mp
    exact RelativeLevi.radical_baseChange_of_dynamic_parabolic
      (hG.baseChange (𝒰.f j)) χ hχ (hr.baseChange_etale (𝒰.f j)) (𝒰.pullbackHom b j)
  let : Smooth U.X.hom := hr.smooth
  refine ⟨hr.isClosedSubgroup.baseChange b, ?_, ?_, ?_⟩
  · change Smooth (pullback.snd U.X.hom b)
    infer_instance
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hr.isNormal.baseChange b
  · intro t
    obtain ⟨j, v, rfl⟩ := Scheme.Cover.exists_eq (𝒰.pullback₁ b) t
    exact (hlocal j).geometricFiber_of_baseChange_at ((𝒰.pullback₁ b).f j)
      (hr.isClosedSubgroup.baseChange b) v

/-- Arbitrary base change preserves every Levi subgroup of a parabolic
of a reductive group, retaining the literal pulled-back inclusion. -/
theorem IsRelativeLeviSubgroup.baseChange_parabolic
    (hl : IsRelativeLeviSubgroup l) (hi : IsRelativeParabolicSubgroup i)
    (hG : IsReductive G) (b : T ⟶ S) :
    IsRelativeLeviSubgroup ((baseChange b).map l) := by
  let : Smooth L.X.hom := hl.smooth
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  refine ⟨hl.isClosedSubgroup.baseChange b, ?_, ?_⟩
  · change Smooth (pullback.snd L.X.hom b)
    infer_instance
  · exact ⟨(baseChange b).obj U, (baseChange b).map r,
      hr.baseChange_parabolic hi hG b,
      RelativeLevi.subgroupMultiplication_isIso_baseChange b l r⟩

namespace RelativeLevi

/-- The actual Levi images of a relative parabolic are stable under the
specified restriction, including the canonical ambient comparison. -/
theorem restrictionStable_of_parabolic
    (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    RestrictionStable P := by
  intro M N a F
  obtain ⟨K, l, hl, hF⟩ := F.exists_presentation
  refine ⟨(baseChange a.left).obj K, TorusSubgroupModuli.familyHom l a, ?_, ?_⟩
  · exact (hl.baseChange_parabolic (hi.baseChange hG M.hom)
      (hG.baseChange M.hom) a.left).comp_iso
      (Descent.pullbackComparison M.hom a.left N.hom (Over.w a) P)
  · rw [← hF, restrictImage_range]

/-- The actual Levi-image presheaf of a relative parabolic in a reductive
group, with no additional base-change hypothesis. -/
def moduliFunctorOfParabolic
    (hi : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  moduliFunctorOfStability (restrictionStable_of_parabolic hi hG)

end RelativeLevi

end Langlands.GroupScheme
