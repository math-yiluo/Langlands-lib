import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalConstructions
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalGluing
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalUniqueness
import Langlands.GroupScheme.SubgroupFunctor.CoverMatching

/-! # Constructing relative radicals from etale-local dynamic presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P : GroupScheme S}

/-- Relative radicals supplied on an etale cover with local dynamic
presentations form a matching family on all relative test schemes. -/
theorem radical_isMatching_of_etale_dynamicCover
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ i, ∃ χ : (Gm (𝒰.X i)).toGrp ⟶ (baseChange (𝒰.f i)).obj G,
      (Dynamic.parabolic χ).IsRepresentedBy ((baseChange (𝒰.f i)).map iP))
    (N : ∀ i, GroupScheme (𝒰.X i))
    (r : ∀ i, N i ⟶ (baseChange (𝒰.f i)).obj P)
    (hr : ∀ i, IsRelativeUnipotentRadical (r i)) :
    SubgroupFunctor.CoverDescent.IsMatching 𝒰 (fun i => SubgroupFunctor.range (r i)) := by
  apply SubgroupFunctor.CoverDescent.isMatching_of_overlap_range_eq 𝒰 N r
  intro i j
  let a := pullback.fst (𝒰.f i) (𝒰.f j)
  let b := pullback.snd (𝒰.f i) (𝒰.f j)
  let : Etale (𝒰.f i) := 𝒰.map_prop i
  let : Etale (𝒰.f j) := 𝒰.map_prop j
  let : Etale a := by dsimp [a]; infer_instance
  let : Etale b := by dsimp [b]; infer_instance
  let : IsAffineHom ((baseChange (𝒰.f i)).obj P).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom (𝒰.f i))
    exact MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom P.X.hom)
  let : IsAffineHom ((baseChange (𝒰.f j)).obj P).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom (𝒰.f j))
    exact MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom P.X.hom)
  obtain ⟨χ, hχ⟩ := hlocal i
  have hχa :
      (Dynamic.parabolic (Dynamic.baseChangeCocharacter a χ)).IsRepresentedBy
        ((baseChange a).map ((baseChange (𝒰.f i)).map iP)) := by
    rw [Dynamic.parabolic_baseChange]
    exact hχ.baseChange a
  exact radical_range_eq_of_dynamic_parabolic hdynamic
    ((hG.baseChange (𝒰.f i)).baseChange a)
    (Dynamic.baseChangeCocharacter a χ) hχa
    ((baseChange a).map (r i))
    ((baseChange b).map (r j) ≫
      (SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 i j P).inv)
    ((hr i).baseChange_etale a)
    (((hr j).baseChange_etale b).comp_iso
      (SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 i j P).symm)

/-- Construct an actual global relative unipotent radical from local dynamic
presentations, conditional on the dynamic relative Levi theorem. -/
def radicalOfEtaleDynamicCover
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (hG : IsReductive G) [IsAffineHom P.X.hom] (iP : P ⟶ G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hlocal : ∀ i, ∃ χ : (Gm (𝒰.X i)).toGrp ⟶ (baseChange (𝒰.f i)).obj G,
      (Dynamic.parabolic χ).IsRepresentedBy ((baseChange (𝒰.f i)).map iP)) :
    Σ U : GroupScheme S, {r : U ⟶ P // IsRelativeUnipotentRadical r} := by
  classical
  choose χ hχ using hlocal
  let R := fun i => dynamicUnipotentRadical hdynamic
    ((baseChange (𝒰.f i)).obj G) ((baseChange (𝒰.f i)).obj P)
    (χ i) ((baseChange (𝒰.f i)).map iP) (hG.baseChange (𝒰.f i)) (hχ i)
  let N := fun i => (R i).1
  let r := fun i => (R i).2.val
  have hr : ∀ i, IsRelativeUnipotentRadical (r i) := fun i => (R i).2.property
  let hmatch := radical_isMatching_of_etale_dynamicCover
    hdynamic hG iP 𝒰 (fun i => ⟨χ i, hχ i⟩) N r hr
  let Q := radicalRepresentativeEtale 𝒰 N r hr hmatch
  exact ⟨Q.val.group, Q.val.hom, Q.property⟩

end Langlands.GroupScheme.RelativeLevi
