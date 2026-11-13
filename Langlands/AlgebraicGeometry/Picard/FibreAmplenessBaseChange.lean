import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionProof
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingProof
import Langlands.AlgebraicGeometry.Picard.ProperFibreSectionShrinking

/-! # Fibre ampleness under arbitrary base change and openness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The points of the base where the specified residue-field fibre bundle is ample. -/
def ampleFibreLocus {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Set S :=
  {s | ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple}

/-- Ampleness descends and ascends across any Cartesian square over a map of fields. -/
lemma isAmple_pullback_iff_of_field_isPullback
    {k K : Type u} [Field k] [Field K]
    {X P : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
    {a : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback a q p b) (L : LineBundle X) :
    ((LineBundle.pullback a).obj L).IsAmple ↔ L.IsAmple := by
  have : IsAffineHom a :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  constructor
  · intro hL
    apply fieldBaseChangeAmpleReflection k K b X p L
    have h' := hL.pullback_of_isAffineHom h.isoPullback.inv
    exact h'.of_iso
      ((Scheme.Modules.pullbackComp h.isoPullback.inv a).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr h.isoPullback_inv_fst).app L.obj)
  · exact fun hL => hL.pullback_of_isAffineHom a

/-- A Cartesian square identifies the new fibre condition with the old one
at the image point, including the induced residue-field extension. -/
lemma mem_ampleFibreLocus_iff_of_isPullback
    {P X T S : Scheme.{u}} {a : P ⟶ X} {q : P ⟶ T}
    {f : X ⟶ S} {b : T ⟶ S} (h : IsPullback a q f b)
    (L : LineBundle X) (t : T) :
    t ∈ ampleFibreLocus q ((LineBundle.pullback a).obj L) ↔
      b t ∈ ampleFibreLocus f L := by
  let m : q.fiber t ⟶ f.fiber (b t) :=
    pullback.map _ _ _ _ a (Spec.map (b.residueFieldMap t)) b
      h.w.symm (by simp)
  have hm : m ≫ f.fiberι (b t) = q.fiberι t ≫ a := by
    simp [m, Scheme.Hom.fiberι]
  have H : IsPullback m (q.fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (b t)) (Spec.map (b.residueFieldMap t)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h t
  let e :
      ((LineBundle.pullback m).obj
        ((LineBundle.pullback (f.fiberι (b t))).obj L)).obj ≅
      ((LineBundle.pullback (q.fiberι t)).obj
        ((LineBundle.pullback a).obj L)).obj :=
    (Scheme.Modules.pullbackComp m (f.fiberι (b t))).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr hm).app L.obj ≪≫
        ((Scheme.Modules.pullbackComp (q.fiberι t) a).app L.obj).symm
  change ((LineBundle.pullback (q.fiberι t)).obj
      ((LineBundle.pullback a).obj L)).IsAmple ↔
    ((LineBundle.pullback (f.fiberι (b t))).obj L).IsAmple
  rw [← isAmple_pullback_iff_of_field_isPullback H]
  exact ⟨fun hL => hL.of_iso e.symm, fun hL => hL.of_iso e⟩

/-- For a proper family over a locally noetherian base, the ample-fibre locus
of any specified line bundle is open. -/
lemma isOpen_ampleFibreLocus
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X) :
    IsOpen (ampleFibreLocus f L) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro s hs
  obtain ⟨V, hsV, hV, hL⟩ := properFibreAmpleSpreading X S f L s hs
  refine ⟨V, ?_, V.isOpen, hsV⟩
  intro t ht
  let t' : V.toScheme := ⟨t, ht⟩
  let : IsAffine V.toScheme := hV
  have : IsAffineHom ((f ∣_ V).fiberι t') := by
    change IsAffineHom (pullback.fst (f ∣_ V) (V.toScheme.fromSpecResidueField t'))
    exact MorphismProperty.pullback_fst _ _ inferInstance
  have ht' : t' ∈ ampleFibreLocus (f ∣_ V)
      ((LineBundle.pullback (f ⁻¹ᵁ V).ι).obj L) :=
    hL.pullback_of_isAffineHom ((f ∣_ V).fiberι t')
  exact (mem_ampleFibreLocus_iff_of_isPullback
    (isPullback_morphismRestrict f V).flip L t').mp ht'

end Langlands.AlgebraicGeometry.Picard
