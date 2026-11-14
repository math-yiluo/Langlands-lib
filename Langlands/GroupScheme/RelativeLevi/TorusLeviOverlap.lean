import Langlands.GroupScheme.RelativeLevi.TorusLeviTransport
import Langlands.GroupScheme.SubgroupFunctor.CoverMatching

/-! # Compatibility of prescribed-torus Levi witnesses on pullback squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

namespace TorusLeviWitness

variable {B S U V : Scheme.{u}} {G P : GroupScheme B} {T : CommGroupScheme B}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Pull a chosen witness across a commuting square and transport it to the
other iterated ambient pullback. -/
def squareTransport (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d)
    (w : TorusLeviWitness (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t))
    (p : TorusDynamicPresentation ((GroupScheme.baseChange b).map i)
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map t))
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G) :
    TorusLeviWitness
      (T := (CommGroupScheme.baseChange e).obj ((CommGroupScheme.baseChange d).obj T))
      ((GroupScheme.baseChange e).map ((GroupScheme.baseChange d).map t)) :=
  (w.baseChange p hDynamic hRadical (hG.baseChange b) c).transport
    (Descent.squareComparison b c d e h P)
    (Descent.squareComparison b c d e h T.toGrp)
    (Descent.squareComparison_naturality b c d e h t).symm

@[simp] theorem squareTransport_group (b : S ⟶ B) (c : V ⟶ S)
    (d : U ⟶ B) (e : V ⟶ U) (h : c ≫ b = e ≫ d)
    (w : TorusLeviWitness (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t))
    (p : TorusDynamicPresentation ((GroupScheme.baseChange b).map i)
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map t))
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G) :
    (w.squareTransport b c d e h p hDynamic hRadical hG).group =
      (GroupScheme.baseChange c).obj w.group := rfl

@[simp] theorem squareTransport_inclusion (b : S ⟶ B) (c : V ⟶ S)
    (d : U ⟶ B) (e : V ⟶ U) (h : c ≫ b = e ≫ d)
    (w : TorusLeviWitness (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t))
    (p : TorusDynamicPresentation ((GroupScheme.baseChange b).map i)
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map t))
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G) :
    (w.squareTransport b c d e h p hDynamic hRadical hG).inclusion =
      (GroupScheme.baseChange c).map w.inclusion ≫ (Descent.squareComparison b c d e h P).hom := rfl

/-- Any two chosen local witnesses agree on a commuting pullback square,
with the second inclusion carried to the first ambient pullback. -/
theorem square_range_eq (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d)
    (w : TorusLeviWitness (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t))
    (w' : TorusLeviWitness (T := (CommGroupScheme.baseChange d).obj T)
      ((GroupScheme.baseChange d).map t))
    (p : TorusDynamicPresentation ((GroupScheme.baseChange b).map i)
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map t))
    (p' : TorusDynamicPresentation ((GroupScheme.baseChange d).map i)
      (T := (CommGroupScheme.baseChange d).obj T) ((GroupScheme.baseChange d).map t))
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G) :
    SubgroupFunctor.range ((GroupScheme.baseChange c).map w.inclusion) =
      SubgroupFunctor.range ((GroupScheme.baseChange e).map w'.inclusion ≫
        (Descent.squareComparison b c d e h P).inv) := by
  let v := w.squareTransport b c d e h p hDynamic hRadical hG
  let v' := w'.baseChange p' hDynamic hRadical (hG.baseChange d) e
  have heq := v.unique v'.group v'.inclusion v'.isLevi v'.contains
  change SubgroupFunctor.range ((GroupScheme.baseChange e).map w'.inclusion) =
    SubgroupFunctor.range ((GroupScheme.baseChange c).map w.inclusion ≫
      (Descent.squareComparison b c d e h P).hom) at heq
  have hback := (SubgroupFunctor.range_comp_iso_eq_iff
    ((GroupScheme.baseChange e).map w'.inclusion)
    ((GroupScheme.baseChange c).map w.inclusion ≫ (Descent.squareComparison b c d e h P).hom)
    (Descent.squareComparison b c d e h P).symm).mpr heq
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    hback.symm

end TorusLeviWitness

namespace EtaleTorusLeviData

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- The actual local Levi inclusions have equal ranges on every pairwise
overlap, after the canonical comparison of iterated pullbacks. -/
theorem overlap_range_eq (D : EtaleTorusLeviData i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G)
    (a b : D.cover.I₀) :
    SubgroupFunctor.range ((GroupScheme.baseChange (pullback.fst (D.cover.f a) (D.cover.f b))).map
      (D.witness a).inclusion) =
    SubgroupFunctor.range ((GroupScheme.baseChange (pullback.snd (D.cover.f a) (D.cover.f b))).map
      (D.witness b).inclusion ≫
        (Descent.squareComparison (D.cover.f a) (pullback.fst _ _)
          (D.cover.f b) (pullback.snd _ _) pullback.condition P).inv) :=
  TorusLeviWitness.square_range_eq (D.cover.f a) (pullback.fst _ _)
    (D.cover.f b) (pullback.snd _ _) pullback.condition
    (D.witness a) (D.witness b) (D.presentation a) (D.presentation b)
    hDynamic hRadical hG

/-- The unique local Levi witnesses form a matching family on all relative tests. -/
theorem isMatching (D : EtaleTorusLeviData i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G) :
    SubgroupFunctor.CoverDescent.IsMatching D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion) :=
  SubgroupFunctor.CoverDescent.isMatching_of_overlap_range_eq D.cover
    (fun a => (D.witness a).group) (fun a => (D.witness a).inclusion)
    (fun a b => D.overlap_range_eq hDynamic hRadical hG a b)

end EtaleTorusLeviData

end Langlands.GroupScheme.RelativeLevi
