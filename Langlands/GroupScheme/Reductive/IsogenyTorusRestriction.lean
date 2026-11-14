import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.FiniteHomCentralizer
import Langlands.GroupScheme.Torus.FiniteImage
import Langlands.GroupScheme.CentralIsogeny.TorusRestrictionIsogeny

/-! # Restrictions of general isogenies to specified maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}

/-- A general isogeny between connected reductive groups restricts to an isogeny
between specified maximal tori in a commuting square. Splitness and centrality
are not required. -/
theorem IsIsogeny.isIsogeny_torusRestriction
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') (hφ : IsIsogeny φ) (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    IsIsogeny (CommGroupScheme.groupHom t) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom G'.X.hom := hG'.isAffineHom
  let : IsFinite φ.hom.hom.left := hφ.1
  let : Surjective φ.hom.hom.left := hφ.2.2
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : IsClosedImmersion i'.hom.hom.left := hi'.2.1
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono i'.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom T'.toGrp.X.hom := hi'.2.1.isAffineHom
  let : Smooth T'.toGrp.X.hom := hi'.1.smooth
  let f := CommGroupScheme.groupHom t
  let : IsFinite f.hom.hom.left :=
    isFinite_torusRestriction hi.2.1 hi'.2.1 φ t ht
  let e := SchematicImage.inclusion f
  let p := SchematicImage.projection f
  let d := e ≫ i'
  have hd : IsClosedSubgroup d := by
    change IsClosedImmersion (e.hom.hom.left ≫ i'.hom.hom.left)
    infer_instance
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let hc : (torusCentralizer i).IsRepresentedBy i :=
    ⟨inferInstance, (maximalTorusCentralizer k G hG T i hi).symm⟩
  let hc' : (torusCentralizer i').IsRepresentedBy i' :=
    ⟨inferInstance, (maximalTorusCentralizer k G' hG' T' i' hi').symm⟩
  have hp : p ≫ d = i ≫ φ := by
    dsimp only [d, p, e]
    rw [← Category.assoc, SchematicImage.projection_inclusion, ← ht]
  have hle : SubgroupFunctor.range (i ≫ φ) ≤ SubgroupFunctor.range d := by
    rw [← hp]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ p.hom.hom, Category.assoc _ _ _⟩
  have hback : SubgroupFunctor.range i' ≤ SubgroupFunctor.range d :=
    range_torusCentralizer_le_of_finiteSurjective φ hi.1 i i' f ht
      i hc i' hc' d hd hle
  let hdrep : (SubgroupFunctor.range d).IsRepresentedBy d := ⟨inferInstance, rfl⟩
  let b := hdrep.factorHom i' hback
  have hb : b ≫ d = i' := hdrep.factorHom_comp i' hback
  have hbe : b ≫ e = 𝟙 T'.toGrp := by
    apply Grp.hom_ext
    apply (cancel_mono i'.hom.hom).mp
    change ((b ≫ e) ≫ i').hom.hom = ((𝟙 T'.toGrp) ≫ i').hom.hom
    rw [Category.assoc, hb, Category.id_comp]
  have heb : e ≫ b = 𝟙 (SchematicImage.image f) := by
    let : Mono e.hom.hom := Over.mono_of_mono_left _
    apply Grp.hom_ext
    apply (cancel_mono e.hom.hom).mp
    change ((e ≫ b) ≫ e).hom.hom = ((𝟙 _) ≫ e).hom.hom
    rw [Category.assoc, hbe, Category.comp_id, Category.id_comp]
  let : IsIso e := ⟨⟨b, heb, hbe⟩⟩
  let : IsIso e.hom.hom.left :=
    (Over.forget _).map_isIso ((Grp.forget _).map e)
  have hpiso : IsIsogeny p := hi.1.isIsogeny_schematicImageProjection f
  let : Flat p.hom.hom.left := hpiso.2.1
  let : Surjective p.hom.hom.left := hpiso.2.2
  have hfac : f.hom.hom.left = p.hom.hom.left ≫ e.hom.hom.left :=
    (congrArg (fun a => a.hom.hom.left) (SchematicImage.projection_inclusion f)).symm
  refine ⟨inferInstance, ?_, ?_⟩
  · change Flat f.hom.hom.left
    rw [hfac]
    infer_instance
  · change Surjective f.hom.hom.left
    rw [hfac]
    infer_instance

/-- A two-sided integer quasiinverse of the restriction of a general isogeny
to specified split maximal tori. -/
def IsIsogeny.torusRestrictionQuasiInverse
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (φ : G ⟶ G') (hφ : IsIsogeny φ) (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    TorusRestrictionQuasiInverse t :=
  Classical.choice (by
    obtain ⟨n, hn, g, hg, hg'⟩ := hT.exists_isogeny_quasiInverse hT' t
      (hφ.isIsogeny_torusRestriction hG hG' hi hi' φ t ht)
    exact ⟨⟨n, hn, g, hg, hg'⟩⟩)

end Langlands.GroupScheme
