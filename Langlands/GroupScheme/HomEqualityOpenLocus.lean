import Langlands.GroupScheme.FppfHomLocality
import Langlands.GroupScheme.Descent.Data

/-! # Gluing equality of group-scheme homomorphisms over open subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace HomEqualityOpenLocus

variable {S T V : Scheme.{u}} {H G : GroupScheme S}

/-- Direct and iterated base change detect the same equality of homomorphisms. -/
theorem iterated_baseChange_eq_iff
    (b : T ⟶ S) (c : V ⟶ T) (d : V ⟶ S) (h : c ≫ b = d) (a a' : H ⟶ G) :
    (baseChange c).map ((baseChange b).map a) =
        (baseChange c).map ((baseChange b).map a') ↔
      (baseChange d).map a = (baseChange d).map a' := by
  let eH := Descent.pullbackComparison b c d h H
  let eG := Descent.pullbackComparison b c d h G
  constructor
  · intro he
    apply (cancel_epi eH.hom).mp
    calc
      eH.hom ≫ (baseChange d).map a =
          (baseChange c).map ((baseChange b).map a) ≫ eG.hom :=
        (Descent.pullbackComparison_naturality b c d h a).symm
      _ = (baseChange c).map ((baseChange b).map a') ≫ eG.hom := by rw [he]
      _ = eH.hom ≫ (baseChange d).map a' :=
        Descent.pullbackComparison_naturality b c d h a'
  · intro he
    apply (cancel_mono eG.hom).mp
    calc
      (baseChange c).map ((baseChange b).map a) ≫ eG.hom =
          eH.hom ≫ (baseChange d).map a :=
        Descent.pullbackComparison_naturality b c d h a
      _ = eH.hom ≫ (baseChange d).map a' := by rw [he]
      _ = (baseChange c).map ((baseChange b).map a') ≫ eG.hom :=
        (Descent.pullbackComparison_naturality b c d h a').symm

/-- Equality after one base change persists along any morphism factoring through it. -/
theorem baseChange_eq_of_factor
    (b : T ⟶ S) (c : V ⟶ T) (d : V ⟶ S) (h : c ≫ b = d)
    {a a' : H ⟶ G} (he : (baseChange b).map a = (baseChange b).map a') :
    (baseChange d).map a = (baseChange d).map a' :=
  (iterated_baseChange_eq_iff b c d h a a').mp (congrArg (baseChange c).map he)

/-- Equality over an open subset gives equality on every residue-field fibre in it. -/
theorem fibre_eq_of_open_eq {a a' : H ⟶ G} (U : S.Opens)
    (he : (baseChange U.ι).map a = (baseChange U.ι).map a') (s : S) (hs : s ∈ U) :
    (baseChange (S.fromSpecResidueField s)).map a =
      (baseChange (S.fromSpecResidueField s)).map a' := by
  have hr : Set.range (S.fromSpecResidueField s) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hs
  exact baseChange_eq_of_factor U.ι
    (IsOpenImmersion.lift U.ι (S.fromSpecResidueField s) hr)
    (S.fromSpecResidueField s) (IsOpenImmersion.lift_fac _ _ _) he

/-- Local equality neighborhoods glue to equality over any open subset that they cover. -/
theorem eq_on_open_of_locally_eq (a a' : H ⟶ G) (U : S.Opens)
    (hloc : ∀ s : U, ∃ W : S.Opens, s.val ∈ W ∧
      (baseChange W.ι).map a = (baseChange W.ι).map a') :
    (baseChange U.ι).map a = (baseChange U.ι).map a' := by
  apply hom_ext_of_pointwise_etale_baseChange
  intro s
  obtain ⟨W, hs, hW⟩ := hloc s
  let Z : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hsZ : s ∈ Z := hs
  have hr : Set.range (Z.ι ≫ U.ι) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact z.property
  let c := IsOpenImmersion.lift W.ι (Z.ι ≫ U.ι) hr
  have he : (baseChange (Z.ι ≫ U.ι)).map a =
      (baseChange (Z.ι ≫ U.ι)).map a' :=
    baseChange_eq_of_factor W.ι c (Z.ι ≫ U.ι)
      (IsOpenImmersion.lift_fac _ _ _) hW
  exact ⟨Z.toScheme, Z.ι, inferInstance, ⟨⟨s, hsZ⟩, rfl⟩,
    (iterated_baseChange_eq_iff U.ι Z.ι (Z.ι ≫ U.ι) rfl a a').mpr he⟩

/-- The fibre equality set is open when equality extends locally at every point of that set. -/
theorem isOpen_fibre_eq_set (a a' : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map a =
          (baseChange (S.fromSpecResidueField s)).map a' →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map a = (baseChange W.ι).map a') :
    IsOpen {s : S | (baseChange (S.fromSpecResidueField s)).map a =
      (baseChange (S.fromSpecResidueField s)).map a'} := by
  rw [isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨W, hsW, hW⟩ := hloc s hs
  exact ⟨W, fun t ht => fibre_eq_of_open_eq W hW t ht, W.isOpen, hsW⟩

/-- The actual open subset consisting exactly of equality fibres, when fibre
equality extends locally. -/
def openLocus (a a' : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map a =
          (baseChange (S.fromSpecResidueField s)).map a' →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map a = (baseChange W.ι).map a') : S.Opens :=
  ⟨_, isOpen_fibre_eq_set a a' hloc⟩

/-- Membership in the constructed open is precisely equality of the two fibres. -/
theorem mem_openLocus_iff (a a' : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map a =
          (baseChange (S.fromSpecResidueField s)).map a' →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map a = (baseChange W.ι).map a') (s : S) :
    s ∈ openLocus a a' hloc ↔
      (baseChange (S.fromSpecResidueField s)).map a =
        (baseChange (S.fromSpecResidueField s)).map a' := Iff.rfl

/-- Under local extension of fibre equality, the equality set is represented by an open
subset over which the two homomorphisms agree. -/
theorem exists_open_fibre_eq_locus (a a' : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map a =
          (baseChange (S.fromSpecResidueField s)).map a' →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map a = (baseChange W.ι).map a') :
    ∃ U : S.Opens,
      (∀ s : S, s ∈ U ↔
        (baseChange (S.fromSpecResidueField s)).map a =
          (baseChange (S.fromSpecResidueField s)).map a') ∧
      (baseChange U.ι).map a = (baseChange U.ι).map a' := by
  let U := openLocus a a' hloc
  exact ⟨U, fun _ => Iff.rfl, eq_on_open_of_locally_eq a a' U
    (fun s => hloc s.val s.property)⟩

end HomEqualityOpenLocus

end Langlands.GroupScheme
