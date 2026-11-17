import Langlands.GroupScheme.Reductive.FiniteCenterOfNoCentralSubgroups
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Quasi-finite neighbourhoods of finite fibres of affine group schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteFibreQuasiFiniteNeighbourhood

section Field

variable {k : Type u} [Field k]

/-- A quasi-finite open chart containing the unit makes an affine finite-type
field group finite, over an algebraically closed field. -/
theorem isFinite_of_open_chart_algClosed [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left] [LocallyQuasiFinite C.hom]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C)
    (he : e ≫ c = η[G.X]) : IsFinite G.X.hom := by
  have : IsLocallyArtinian C.left := .of_locallyQuasiFinite C.hom
  let x := e.left (IdentityComponent.basePoint k)
  have hx : c.left x = IdentityComponent.identityPoint G :=
    congrArg (fun a => a.left (IdentityComponent.basePoint k)) he
  have hopen : IsOpen ({c.left x} : Set G.X.left) := by
    rw [← Set.image_singleton]
    exact c.left.isOpenMap _ (isOpen_discrete _)
  rw [hx] at hopen
  exact FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton G _ hopen

/-- A quasi-finite open chart containing the unit makes an affine finite-type
field group finite over any field. -/
theorem isFinite_of_open_chart
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {C : Over (Spec (CommRingCat.of k))} (c : C ⟶ G.X)
    [IsOpenImmersion c.left] [LocallyQuasiFinite C.hom]
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C)
    (he : e ≫ c = η[G.X]) : IsFinite G.X.hom := by
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback b
  let G' := (GroupScheme.baseChange b).obj G
  let c' := F.map c
  let e' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ F.obj C :=
    Functor.LaxMonoidal.ε F ≫ F.map e
  have he' : e' ≫ c' = η[G'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map e) ≫ F.map c = _
    rw [Category.assoc, ← F.map_comp, he]
    rfl
  have hc' : IsOpenImmersion c'.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b c inferInstance
  have hq' : LocallyQuasiFinite (F.obj C).hom := by
    change LocallyQuasiFinite (pullback.snd C.hom b)
    infer_instance
  have : IsAffineHom G'.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have hfin : IsFinite G'.X.hom :=
    @isFinite_of_open_chart_algClosed K _ _ G' ‹_› ‹_› (F.obj C) c' hc' hq' e' he'
  change IsFinite (pullback.snd G.X.hom b) at hfin
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc k K
  let : Surjective b := hs
  let : Flat b := hf
  let : QuasiCompact b := hqc
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfin

end Field

/-- An affine finite-type group with a quasi-finite open chart containing the
whole unit section is locally quasi-finite. -/
theorem locallyQuasiFinite_of_open_chart {S : Scheme.{u}}
    (G : GroupScheme S) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {C : Over S} (c : C ⟶ G.X) [IsOpenImmersion c.left]
    [LocallyQuasiFinite C.hom] (e : 𝟙_ (Over S) ⟶ C)
    (he : e ≫ c = η[G.X]) : LocallyQuasiFinite G.X.hom := by
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro s
  let b := S.fromSpecResidueField s
  let F := Over.pullback b
  let G' := (GroupScheme.baseChange b).obj G
  let c' := F.map c
  let e' : 𝟙_ (Over (Spec (S.residueField s))) ⟶ F.obj C :=
    Functor.LaxMonoidal.ε F ≫ F.map e
  have he' : e' ≫ c' = η[G'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map e) ≫ F.map c = _
    rw [Category.assoc, ← F.map_comp, he]
    rfl
  have hc' : IsOpenImmersion c'.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b c inferInstance
  have hq' : LocallyQuasiFinite (F.obj C).hom := by
    change LocallyQuasiFinite (pullback.snd C.hom b)
    infer_instance
  have : IsAffineHom G'.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : IsFinite G'.X.hom :=
    @isFinite_of_open_chart (S.residueField s) _ G' ‹_› ‹_› (F.obj C) c' hc' hq' e' he'
  exact inferInstanceAs (LocallyQuasiFinite G'.X.hom)

private theorem unit_baseChange_fst {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) :
    η[((GroupScheme.baseChange b).obj G).X].left ≫ pullback.fst G.X.hom b =
      b ≫ η[G.X].left := by
  change (Functor.LaxMonoidal.ε (Over.pullback b) ≫
    (Over.pullback b).map η[G.X]).left ≫ _ = _
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
    Over.ε_pullback_left]
  rw [← Category.assoc]
  congr 1
  change inv (pullback.snd (𝟙 S) b) ≫ pullback.fst (𝟙 S) b = b
  apply (cancel_epi (pullback.snd (𝟙 S) b)).mp
  simp only [IsIso.hom_inv_id_assoc]
  simpa using (pullback.condition (f := 𝟙 S) (g := b))

/-- The inverse image of the quasi-finite locus under the unit section. -/
def quasiFiniteUnitLocus {S : Scheme.{u}} (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : S.Opens :=
  η[G.X].left ⁻¹ᵁ G.X.hom.quasiFiniteLocus

/-- Over the unit's quasi-finite locus, the whole affine finite-type group is
locally quasi-finite. -/
theorem locallyQuasiFinite_baseChange_quasiFiniteUnitLocus {S : Scheme.{u}}
    (G : GroupScheme S) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    LocallyQuasiFinite
      ((GroupScheme.baseChange (quasiFiniteUnitLocus G).ι).obj G).X.hom := by
  let Q := G.X.hom.quasiFiniteLocus
  let C : Over S := Over.mk (Q.ι ≫ G.X.hom)
  let c : C ⟶ G.X := Over.homMk Q.ι
  have : IsOpenImmersion c.left := inferInstanceAs (IsOpenImmersion Q.ι)
  have : LocallyQuasiFinite C.hom :=
    inferInstanceAs (LocallyQuasiFinite (Q.ι ≫ G.X.hom))
  let U := quasiFiniteUnitLocus G
  let F := Over.pullback U.ι
  let G' := (GroupScheme.baseChange U.ι).obj G
  let c' := F.map c
  let a : U.toScheme ⟶ C.left := η[G.X].left ∣_ Q
  have ha : a ≫ C.hom = U.ι := by
    change (η[G.X].left ∣_ Q) ≫ Q.ι ≫ G.X.hom = U.ι
    rw [morphismRestrict_ι_assoc, Over.w]
    exact Category.comp_id _
  let e' : 𝟙_ (Over U.toScheme) ⟶ F.obj C :=
    Over.homMk (pullback.lift a (𝟙 U.toScheme) (by simpa using ha)) (by
      change pullback.lift _ _ _ ≫ pullback.snd C.hom U.ι = _
      exact pullback.lift_snd _ _ _)
  have he' : e' ≫ c' = η[G'.X] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (e'.left ≫ c'.left) ≫ pullback.fst G.X.hom U.ι = _
      calc
        (e'.left ≫ c'.left) ≫ pullback.fst G.X.hom U.ι = a ≫ Q.ι := by
          change (pullback.lift a (𝟙 U.toScheme) _) ≫
            (pullback.lift _ _ _) ≫ pullback.fst G.X.hom U.ι = _
          rw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
          rfl
        _ = U.ι ≫ η[G.X].left := morphismRestrict_ι _ _
        _ = η[G'.X].left ≫ pullback.fst G.X.hom U.ι :=
          (unit_baseChange_fst U.ι G).symm
    · exact (e' ≫ c').w.trans η[G'.X].w.symm
  have hc' : IsOpenImmersion c'.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) U.ι c inferInstance
  have : LocallyQuasiFinite (F.obj C).hom := by
    change LocallyQuasiFinite (pullback.snd C.hom U.ι)
    infer_instance
  have : IsAffineHom G'.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom U.ι)
    exact MorphismProperty.pullback_snd G.X.hom U.ι
      (inferInstance : IsAffineHom G.X.hom)
  have : LocallyOfFiniteType G'.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom U.ι)
    infer_instance
  let : IsOpenImmersion c'.left := hc'
  exact locallyQuasiFinite_of_open_chart G' c' e' he'

/-- A finite residue-field fibre places the base point in the unit's
quasi-finite locus. -/
theorem mem_quasiFiniteUnitLocus_of_isFinite_fibre {S : Scheme.{u}}
    (G : GroupScheme S) [LocallyOfFiniteType G.X.hom] (s : S)
    (hs : IsFinite ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G).X.hom) :
    s ∈ quasiFiniteUnitLocus G := by
  have : IsFinite (G.X.hom.fiberToSpecResidueField s) := hs
  have : IsLocallyArtinian (G.X.hom.fiber s) :=
    .of_locallyQuasiFinite (G.X.hom.fiberToSpecResidueField s)
  have he : G.X.hom (η[G.X].left s) = s :=
    congrArg (fun a : S ⟶ S => a s) η[G.X].w
  change G.X.hom.QuasiFiniteAt (η[G.X].left s)
  apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
  have : DiscreteTopology (G.X.hom.fiber (G.X.hom (η[G.X].left s))) := by
    rw [he]
    infer_instance
  exact isOpen_discrete _

/-- SGA 3 IX, Lemma 6.3 for affine groups locally of finite type: a finite fibre
has an open base neighbourhood over which the group is locally quasi-finite. -/
theorem exists_locallyQuasiFinite_neighbourhood_of_isFinite_fibre {S : Scheme.{u}}
    (G : GroupScheme S) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (s : S)
    (hs : IsFinite ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G).X.hom) :
    ∃ U : S.Opens, s ∈ U ∧ LocallyQuasiFinite ((GroupScheme.baseChange U.ι).obj G).X.hom :=
  ⟨quasiFiniteUnitLocus G, mem_quasiFiniteUnitLocus_of_isFinite_fibre G s hs,
    locallyQuasiFinite_baseChange_quasiFiniteUnitLocus G⟩

end Langlands.GroupScheme.FiniteFibreQuasiFiniteNeighbourhood
