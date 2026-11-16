import Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleDualPullback

/-! # Duals of coherent line bundles on presheaves -/

noncomputable section
universe u v
open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

private lemma dualPullbackIso_composition_inv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : LineBundle Z) :
    LineBundle.dualPullbackIso (f ≫ g) L ≪≫
        LineBundle.dualIso ((LineBundle.pullbackComp f g).app L).symm =
      ((LineBundle.pullbackComp f g).app L.dual).symm ≪≫
        (LineBundle.pullback f).mapIso (LineBundle.dualPullbackIso g L) ≪≫
          LineBundle.dualPullbackIso f ((LineBundle.pullback g).obj L) := by
  apply Iso.ext
  have h := congrArg Iso.hom (LineBundle.dualPullbackIso_composition f g L)
  simp only [Iso.trans_hom] at h
  apply (cancel_epi ((LineBundle.pullbackComp f g).app L.dual).hom).1
  apply (cancel_mono (LineBundle.dualIso ((LineBundle.pullbackComp f g).app L)).hom).1
  simpa only [Iso.trans_hom, LineBundle.dualIso_symm, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h.symm

namespace PresheafLineBundle

/-- Dualize every actual family line bundle with canonical coherent pullback maps. -/
def dual (L : PresheafLineBundle F) : PresheafLineBundle F where
  bundle T x := (L.bundle T x).dual
  pullbackIso a x y h := LineBundle.dualPullbackIso a.left (L.bundle _ x) ≪≫
    LineBundle.dualIso (L.pullbackIso a x y h)
  pullbackIso_id T x := by
    rw [L.pullbackIso_id]
    exact LineBundle.dualPullbackIso_identity (L.bundle T x)
  pullbackIso_comp a b x y z hb ha := by
    rw [L.pullbackIso_comp a b x y z hb ha]
    simp only [← LineBundle.dualIso_comp, Over.comp_left]
    rw [← Iso.trans_assoc,
      dualPullbackIso_composition_inv a.left b.left (L.bundle _ x)]
    simp only [Iso.trans_assoc, Functor.mapIso_trans]
    have hn := congrArg
      (fun e => ((LineBundle.pullbackComp a.left b.left).app
          (L.bundle _ x).dual).symm ≪≫
        (LineBundle.pullback a.left).mapIso
          (LineBundle.dualPullbackIso b.left (L.bundle _ x)) ≪≫
        e ≪≫ LineBundle.dualIso (L.pullbackIso a y z ha))
      (LineBundle.dualPullbackIso_naturality a.left (L.pullbackIso b x y hb))
    simpa only [Iso.trans_assoc] using hn.symm

@[simp]
lemma dual_bundle (L : PresheafLineBundle F) (T : Over S) (x : F.obj (op T)) :
    L.dual.bundle T x = (L.bundle T x).dual := rfl

end PresheafLineBundle
end Langlands.AlgebraicGeometry.Picard
