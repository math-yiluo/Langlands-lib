import Langlands.GroupScheme.Descent.SemilinearDatum
import Langlands.GroupScheme.Rational.UnipotentRadicalDescent

/-! # Semilinear recovery of an actual descent solution -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} {p : S ⟶ B} {H : GroupScheme S}
  {D : Datum p H} (s : Solution D)

/-- The transport of the descended object induces an actual semilinear
isomorphism on the object supplied by the solution. -/
def Solution.semilinearIso (a : S ⟶ S) (ha : a ≫ p = p) :
    (baseChange a).obj H ≅ H :=
  ((baseChange a).mapIso s.iso).symm ≪≫
    descentBaseChangeIso p a ha s.obj ≪≫ s.iso

/-- A solution intertwines each normalized component of its datum with
canonical semilinear transport on the descended object. -/
theorem Solution.semilinear (a : S ⟶ S) (ha : a ≫ p = p)
    (q : S ⟶ Overlap p) (hf : q ≫ fst p = 𝟙 S) (hg : q ≫ snd p = a)
    (e : (baseChange a).obj H ≅ H)
    (he : pullIso q hf hg D.overlap = semilinearComponent H e) :
    (baseChange a).map s.iso.hom ≫ e.hom =
      (descentBaseChangeIso p a ha s.obj).hom ≫ s.iso.hom := by
  have hc := congrArg (pullHom q hf hg) s.compatible
  dsimp only [canonicalDatum] at hc
  rw [pullHom_comp q hf hf hg, pullHom_map,
    pullHom_comp q hf hg hg, pullHom_map, ← pullIso_hom, ← pullIso_hom,
    he, pullIso_canonicalOverlap_eq p s.obj a ha] at hc
  have hid : (baseChange (𝟙 S)).map s.iso.hom ≫ (baseChangeIdIso H).hom =
      (baseChangeIdIso ((baseChange p).obj s.obj)).hom ≫ s.iso.hom :=
    (((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality
      s.iso.hom)
  simp only [semilinearComponent, Iso.trans_hom, Iso.symm_hom] at hc
  rw [← Category.assoc, hid, Category.assoc, Category.assoc, cancel_epi] at hc
  apply (cancel_epi (descentBaseChangeIso p a ha s.obj).inv).mp
  apply (cancel_mono e.inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using hc.symm

/-- A normalized component of the datum recovers the induced semilinear
isomorphism of its actual solution. -/
theorem Solution.semilinearIso_eq (a : S ⟶ S) (ha : a ≫ p = p)
    (q : S ⟶ Overlap p) (hf : q ≫ fst p = 𝟙 S) (hg : q ≫ snd p = a)
    (e : (baseChange a).obj H ≅ H)
    (he : pullIso q hf hg D.overlap = semilinearComponent H e) :
    s.semilinearIso a ha = e := by
  apply Iso.ext
  apply (cancel_epi ((baseChange a).mapIso s.iso).hom).mp
  change ((baseChange a).mapIso s.iso).hom ≫
    (((baseChange a).mapIso s.iso).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]
  exact (s.semilinear a ha q hf hg e he).symm

end Langlands.GroupScheme.Descent
