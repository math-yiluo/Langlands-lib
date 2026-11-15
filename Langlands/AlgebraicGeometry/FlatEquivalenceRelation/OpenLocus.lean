import Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Classifier
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # The open locus of the Hilbert scheme over which the classified family lies in an open

Let `C` be a Hilbert scheme of a proper morphism `f : X ⟶ S` and `U` an open subscheme of `X`.
The points of `H` whose fibre of the universal closed subscheme `D` lies in `U` form an open
subscheme `C.locus U`. This is the complement of the image of the closed set `D \ U` under
the proper map `D ⟶ H`.

Let `i : Z ⟶ X` be an immersion and `U` the largest open subscheme in which `i` is closed.
The classifying morphism `φ : Z ⟶ H` of a flat proper equivalence relation on `Z` lands in
`C.locus U`. Over this locus the graph `Z ⟶ D` of `φ` is a closed immersion. Nitsure,
*Construction of Hilbert and Quot schemes*, Theorem 6.8, uses the Hilbert scheme of `Z` itself,
whose graph is closed. The open locus is needed here because `X` is a projective space
containing `Z`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.FlatEquivalenceRelation

open _root_.AlgebraicGeometry

namespace Classifier

variable {X S : Scheme.{u}} {f : X ⟶ S} (C : Classifier f)

/-- The universal closed subscheme, mapped to `X`. -/
noncomputable abbrev toX : C.D ⟶ X := C.ιD ≫ pullback.fst f C.πH

/-- The open subscheme of `H` of the points whose fibre of the universal closed subscheme lies
in `U`. -/
noncomputable def locus [IsProper f] (U : X.Opens) : C.H.Opens where
  carrier := (C.pD '' (C.toX ⁻¹' (U : Set X)ᶜ))ᶜ
  is_open' := by
    have := C.isProper_pD
    exact (C.pD.isClosedMap _
      (U.isOpen.isClosed_compl.preimage C.toX.continuous)).isOpen_compl

theorem mem_locus [IsProper f] {U : X.Opens} {y : C.H} :
    y ∈ C.locus U ↔ ∀ d : C.D, C.pD d = y → C.toX d ∈ U := by
  change y ∈ (C.pD '' (C.toX ⁻¹' (U : Set X)ᶜ))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and,
    SetLike.mem_coe]
  exact forall_congr' fun d => by tauto

theorem toX_mem_of_mem_locus [IsProper f] {U : X.Opens} (d : C.D) (hd : C.pD d ∈ C.locus U) :
    C.toX d ∈ U :=
  (C.mem_locus.mp hd) d rfl

/-- The universal closed subscheme over the locus `C.locus U`. -/
noncomputable abbrev Dl [IsProper f] (U : X.Opens) : Scheme.{u} := (C.pD ⁻¹ᵁ C.locus U).toScheme

/-- The universal family over the locus `C.locus U`. -/
noncomputable abbrev pDl [IsProper f] (U : X.Opens) : C.Dl U ⟶ C.locus U := C.pD ∣_ C.locus U

instance [IsProper f] (U : X.Opens) : Flat (C.pDl U) := by
  have := C.flat_pD
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict C.pD (C.locus U)).flip this

instance [IsProper f] (U : X.Opens) : IsProper (C.pDl U) := by
  have := C.isProper_pD
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict C.pD (C.locus U)).flip this

instance [IsProper f] (U : X.Opens) : LocallyOfFinitePresentation (C.pDl U) := by
  have := C.locallyOfFinitePresentation_pD
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict C.pD (C.locus U)).flip this

/-- The universal closed subscheme over the locus `C.locus U`, mapped to `U`. -/
noncomputable def toU [IsProper f] (U : X.Opens) : C.Dl U ⟶ U :=
  IsOpenImmersion.lift U.ι ((C.pD ⁻¹ᵁ C.locus U).ι ≫ C.toX) (by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact C.toX_mem_of_mem_locus _ d.2)

@[reassoc (attr := simp)]
theorem toU_ι [IsProper f] (U : X.Opens) :
    C.toU U ≫ U.ι = (C.pD ⁻¹ᵁ C.locus U).ι ≫ C.toX :=
  IsOpenImmersion.lift_fac _ _ _

theorem isSeparated_toU [IsProper f] [IsSeparated C.πH] (U : X.Opens) :
    IsSeparated (C.toU U) := by
  have : IsSeparated (C.toU U ≫ U.ι) := by rw [toU_ι]; infer_instance
  exact IsSeparated.of_comp (C.toU U) U.ι

end Classifier

section Locus

variable {X S Z R : Scheme.{u}} {f : X ⟶ S} (C : Classifier f) {p : Z ⟶ S} {s t : R ⟶ Z}
  {i : Z ⟶ X} {hi : i ≫ f = p} {h : s ≫ p = t ≫ p}
  [IsClosedImmersion (family s t i hi h)]
  {φ : Z ⟶ C.H} {hφ : φ ≫ C.πH = p}
  (hEq : ∀ T : Scheme.{u}, Equivalence (@Rel R Z s t T)) [Mono i]
  (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker)

omit [Mono i] in
@[reassoc (attr := simp)]
theorem graph_toX : graph C hEq hW ≫ C.toX = i := by
  simp [Classifier.toX]

include hEq hW in
/-- **The classifying morphism lands in the open locus.** If `i` lands in the open `U`, then
`φ` lands in `C.locus U`: every point of the fibre of `D` over `φ z` is `i (t r)` for some
`r : R`. -/
theorem range_subset_locus [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) :
    Set.range φ ⊆ C.locus U := by
  rintro _ ⟨z, rfl⟩
  rw [SetLike.mem_coe, C.mem_locus]
  intro d hd
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z d hd.symm
  obtain ⟨c, -, hct⟩ := exists_factor C hEq hW (pullback.fst φ C.pD) (pullback.snd φ C.pD)
    pullback.condition
  have he : pullback.snd φ C.pD ≫ C.toX = c ≫ t ≫ i := by
    rw [← hct]; simp
  rw [← hw2, ← Scheme.Hom.comp_apply, he]
  exact hU ⟨_, rfl⟩

include hEq hW in
/-- The classifying morphism, as a morphism into the open locus. -/
noncomputable def φl [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) : Z ⟶ C.locus U :=
  IsOpenImmersion.lift (C.locus U).ι φ (by
    rw [Scheme.Opens.range_ι]; exact range_subset_locus C hEq hW U hU)

@[reassoc (attr := simp)]
theorem φl_ι [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) :
    φl C hEq hW U hU ≫ (C.locus U).ι = φ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The graph of the classifying morphism, as a morphism into the universal closed subscheme
over the open locus. -/
noncomputable def graphl [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) : Z ⟶ C.Dl U :=
  IsOpenImmersion.lift (C.pD ⁻¹ᵁ C.locus U).ι (graph C hEq hW) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change C.pD (graph C hEq hW z) ∈ C.locus U
    rw [← Scheme.Hom.comp_apply, graph_pD]
    exact range_subset_locus C hEq hW U hU ⟨z, rfl⟩)

@[reassoc (attr := simp)]
theorem graphl_ι [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) :
    graphl C hEq hW U hU ≫ (C.pD ⁻¹ᵁ C.locus U).ι = graph C hEq hW :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem graphl_pDl [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) :
    graphl C hEq hW U hU ≫ C.pDl U = φl C hEq hW U hU := by
  rw [← cancel_mono (C.locus U).ι, Category.assoc, morphismRestrict_ι, graphl_ι_assoc,
    graph_pD, φl_ι]

@[reassoc (attr := simp)]
theorem graphl_toU [IsProper f] (U : X.Opens) (hU : Set.range i ⊆ U) :
    graphl C hEq hW U hU ≫ C.toU U = IsOpenImmersion.lift U.ι i (by
      rw [Scheme.Opens.range_ι]; exact hU) := by
  rw [← cancel_mono U.ι, Category.assoc, Classifier.toU_ι, graphl_ι_assoc, graph_toX,
    IsOpenImmersion.lift_fac]

theorem range_subset_coborderRange (i : Z ⟶ X) [IsImmersion i] :
    Set.range i ⊆ (i.coborderRange : Set X) :=
  subset_coborder

/-- **The graph is a closed immersion over the open locus**, when `U` is the largest open
subscheme of `X` in which the immersion `i` is closed. -/
theorem isClosedImmersion_graphl [IsProper f] [IsSeparated C.πH] [IsImmersion i] :
    IsClosedImmersion (graphl C hEq hW i.coborderRange (range_subset_coborderRange i)) := by
  have := C.isSeparated_toU i.coborderRange
  have : IsClosedImmersion (graphl C hEq hW i.coborderRange (range_subset_coborderRange i) ≫
      C.toU i.coborderRange) := by
    rw [graphl_toU]
    exact inferInstanceAs (IsClosedImmersion i.liftCoborder)
  exact IsClosedImmersion.of_comp _ (C.toU i.coborderRange)

end Locus

end Langlands.AlgebraicGeometry.FlatEquivalenceRelation
