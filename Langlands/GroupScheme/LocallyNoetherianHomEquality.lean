import Langlands.GroupScheme.SchematicHomEquality

/-! # Closed fibre equality loci over locally Noetherian bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.GroupScheme.LocallyNoetherianHomEquality

variable {S T : Scheme.{u}} {H G : GroupScheme S}

/-- Base change along an isomorphism detects equality of group-scheme homomorphisms. -/
theorem baseChange_hom_ext_of_isIso (b : T ⟶ S) [IsIso b] {f g : H ⟶ G}
    (he : (baseChange b).map f = (baseChange b).map g) : f = g :=
  (baseChange b).map_injective he

/-- Fibre equality for an open base change is equality on the fibre over the image point. -/
theorem fibre_eq_baseChange_iff (b : T ⟶ S) [IsOpenImmersion b]
    (f g : H ⟶ G) (t : T) :
    (baseChange (T.fromSpecResidueField t)).map ((baseChange b).map f) =
        (baseChange (T.fromSpecResidueField t)).map ((baseChange b).map g) ↔
      (baseChange (S.fromSpecResidueField (b t))).map f =
        (baseChange (S.fromSpecResidueField (b t))).map g := by
  let r := S.fromSpecResidueField (b t)
  let c := Spec.map (b.residueFieldMap t)
  have h : T.fromSpecResidueField t ≫ b = c ≫ r :=
    (b.SpecMap_residueFieldMap_fromSpecResidueField t).symm
  rw [HomEqualityOpenLocus.iterated_baseChange_eq_iff b
    (T.fromSpecResidueField t) (c ≫ r) h f g]
  constructor
  · intro he
    exact baseChange_hom_ext_of_isIso c
      ((HomEqualityOpenLocus.iterated_baseChange_eq_iff r c (c ≫ r) rfl f g).mpr he)
  · intro he
    exact HomEqualityOpenLocus.baseChange_eq_of_factor r c (c ≫ r) rfl he

/-- Local extension of fibre equality persists after an open base change. -/
theorem local_extension_baseChange (b : T ⟶ S) [IsOpenImmersion b]
    (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g)
    (t : T)
    (ht : (baseChange (T.fromSpecResidueField t)).map ((baseChange b).map f) =
      (baseChange (T.fromSpecResidueField t)).map ((baseChange b).map g)) :
    ∃ V : T.Opens, t ∈ V ∧
      (baseChange V.ι).map ((baseChange b).map f) =
        (baseChange V.ι).map ((baseChange b).map g) := by
  obtain ⟨W, htW, hW⟩ := hloc (b t) ((fibre_eq_baseChange_iff b f g t).mp ht)
  let V : T.Opens := b ⁻¹ᵁ W
  refine ⟨V, htW, ?_⟩
  apply (HomEqualityOpenLocus.iterated_baseChange_eq_iff b V.ι
    (V.ι ≫ b) rfl f g).mpr
  have hr : Set.range (V.ι ≫ b) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact x.property
  exact HomEqualityOpenLocus.baseChange_eq_of_factor W.ι
    (IsOpenImmersion.lift W.ι (V.ι ≫ b) hr) (V.ι ≫ b)
    (IsOpenImmersion.lift_fac _ _ _) hW

/-- Over a locally Noetherian base, fibre equality has a closed locus whenever
the source is flat, the target separated, and fibre equality extends locally. -/
theorem isClosed_fibre_eq_set [IsLocallyNoetherian S]
    [Flat H.X.hom] [IsSeparated G.X.hom] (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) :
    IsClosed {s : S | (baseChange (S.fromSpecResidueField s)).map f =
      (baseChange (S.fromSpecResidueField s)).map g} := by
  let E : Set S := {s | (baseChange (S.fromSpecResidueField s)).map f =
    (baseChange (S.fromSpecResidueField s)).map g}
  suffices IsOpen Eᶜ from isOpen_compl_iff.mp this
  rw [isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨i, t, rfl⟩ := S.affineOpenCover.openCover.exists_eq s
  let B := S.affineOpenCover.openCover.X i
  let b : B ⟶ S := S.affineOpenCover.openCover.f i
  have : IsAffine B := Scheme.isAffine_affineCover S i
  have : IsNoetherian B := _root_.AlgebraicGeometry.IsNoetherian.mk
  have : Flat ((baseChange b).obj H).X.hom := by
    change Flat (CategoryTheory.Limits.pullback.snd H.X.hom b)
    infer_instance
  have : IsSeparated ((baseChange b).obj G).X.hom := by
    change IsSeparated (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hclosed : IsClosed (b ⁻¹' E) := by
    have h := SchematicHomEquality.isClosed_fibre_eq_set_of_locally_eq
      ((baseChange b).map f) ((baseChange b).map g)
      (local_extension_baseChange b f g hloc)
    have he : b ⁻¹' E =
        {t : B | (baseChange (B.fromSpecResidueField t)).map ((baseChange b).map f) =
          (baseChange (B.fromSpecResidueField t)).map ((baseChange b).map g)} := by
      ext t
      exact (fibre_eq_baseChange_iff b f g t).symm
    exact he ▸ h
  refine ⟨b '' (b ⁻¹' Eᶜ), Set.image_preimage_subset b Eᶜ,
    b.isOpenMap _ ?_, ⟨t, hs, rfl⟩⟩
  simpa only [Set.preimage_compl] using hclosed.isOpen_compl

/-- The actual clopen equality locus of the residue-field fibres. -/
def clopenLocus [IsLocallyNoetherian S] [Flat H.X.hom] [IsSeparated G.X.hom]
    (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) : Clopens S :=
  ⟨_, ⟨isClosed_fibre_eq_set f g hloc,
    HomEqualityOpenLocus.isOpen_fibre_eq_set f g hloc⟩⟩

/-- Membership in the canonical clopen is exactly equality of the two fibres. -/
theorem mem_clopenLocus_iff [IsLocallyNoetherian S]
    [Flat H.X.hom] [IsSeparated G.X.hom] (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) (s : S) :
    s ∈ clopenLocus f g hloc ↔
      (baseChange (S.fromSpecResidueField s)).map f =
        (baseChange (S.fromSpecResidueField s)).map g := Iff.rfl

/-- The fibre equality locus is clopen, and the homomorphisms agree over it,
under the same locally Noetherian hypotheses. -/
theorem exists_clopen_fibre_eq_locus [IsLocallyNoetherian S]
    [Flat H.X.hom] [IsSeparated G.X.hom] (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) :
    ∃ U : S.Opens, IsClosed (U : Set S) ∧
      (∀ s : S, s ∈ U ↔
        (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g) ∧
      (baseChange U.ι).map f = (baseChange U.ι).map g := by
  let U : S.Opens := (clopenLocus f g hloc).toOpens
  exact ⟨U, (clopenLocus f g hloc).isClosed, fun _ => Iff.rfl,
    HomEqualityOpenLocus.eq_on_open_of_locally_eq f g U (fun s => hloc s.val s.property)⟩

end Langlands.GroupScheme.LocallyNoetherianHomEquality
