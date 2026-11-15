import Langlands.AlgebraicGeometry.FlatEquivalenceRelation.OpenLocus
import Langlands.AlgebraicGeometry.KernelFlatBaseChange

/-! # The quotient by a flat proper equivalence relation, inside the Hilbert scheme

We keep the setting of `Langlands.AlgebraicGeometry.FlatEquivalenceRelation.OpenLocus`. The
immersion is `i : Z ⟶ X`, and `U` is the largest open subscheme of `X` in which `i` is closed.
Let `φ'' : Z ⟶ H''` be the classifying morphism into the open locus `H'' = C.locus U`. The
quotient `Q` is the scheme-theoretic image of `φ''`, and `π : Z ⟶ Q` is the induced morphism.

The graph `Z ⟶ D''` of `φ''` is a closed immersion over `H''`. Flat base change of kernels
along the flat morphism `D'' ⟶ H''` shows that `Z = D'' ×_{H''} Q`. Hence `π` is flat,
proper and locally of finite presentation, as a base change of `D'' ⟶ H''`. It is surjective,
being universally closed and dominant. The relation `R` is `Z ×_Q Z`, because `φ` detects
the relation. This is the proof of Nitsure, *Construction of Hilbert and Quot schemes*,
Theorem 6.8, except for quasi-projectivity of `Q`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.FlatEquivalenceRelation

open _root_.AlgebraicGeometry

section Quotient

variable {X S Z R : Scheme.{u}} {f : X ⟶ S} (C : Classifier f) {p : Z ⟶ S} {s t : R ⟶ Z}
  {i : Z ⟶ X} {hi : i ≫ f = p} {h : s ≫ p = t ≫ p}
  [IsClosedImmersion (family s t i hi h)]
  {φ : Z ⟶ C.H} {hφ : φ ≫ C.πH = p}
  (hEq : ∀ T : Scheme.{u}, Equivalence (@Rel R Z s t T)) [Mono i]
  (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker)
  [IsProper f] [IsSeparated C.πH] [IsImmersion i]

/-- The classifying morphism into the open locus `H''`. -/
noncomputable abbrev φq : Z ⟶ C.locus i.coborderRange :=
  φl C hEq hW i.coborderRange (range_subset_coborderRange i)

/-- The graph `Z ⟶ D''` of the classifying morphism, over the open locus. -/
noncomputable abbrev Γq : Z ⟶ C.Dl i.coborderRange :=
  graphl C hEq hW i.coborderRange (range_subset_coborderRange i)

instance : IsClosedImmersion (Γq C hEq hW) := isClosedImmersion_graphl C hEq hW

theorem quasiCompact_φq [QuasiCompact p] : QuasiCompact (φq C hEq hW) := by
  have : QuasiCompact (φq C hEq hW ≫ (C.locus i.coborderRange).ι ≫ C.πH) := by
    rw [φl_ι_assoc, hφ]; infer_instance
  exact QuasiCompact.of_comp _ ((C.locus i.coborderRange).ι ≫ C.πH)

/-- The quotient: the scheme-theoretic image of the classifying morphism. -/
noncomputable abbrev Q : Scheme.{u} := (φq C hEq hW).image

/-- The quotient morphism. -/
noncomputable abbrev π : Z ⟶ Q C hEq hW := (φq C hEq hW).toImage

/-- The inclusion of the quotient into the open locus of the Hilbert scheme. -/
noncomputable abbrev ιQ : Q C hEq hW ⟶ C.locus i.coborderRange := (φq C hEq hW).imageι

omit [IsSeparated C.πH] in
/-- The kernel of the projection `Z ×_{H''} D'' ⟶ D''` is the kernel of the graph. -/
theorem ker_pullback_snd :
    (pullback.snd (φq C hEq hW) (C.pDl i.coborderRange)).ker = (Γq C hEq hW).ker := by
  apply le_antisymm
  · let σ : Z ⟶ pullback (φq C hEq hW) (C.pDl i.coborderRange) :=
      pullback.lift (𝟙 Z) (Γq C hEq hW) (by rw [Category.id_comp, graphl_pDl])
    have hσ : σ ≫ pullback.snd _ _ = Γq C hEq hW := pullback.lift_snd _ _ _
    rw [← hσ]
    exact Scheme.Hom.le_ker_comp _ _
  · have hab : pullback.fst (φq C hEq hW) (C.pDl i.coborderRange) ≫ φ =
        (pullback.snd (φq C hEq hW) (C.pDl i.coborderRange) ≫
          (C.pD ⁻¹ᵁ C.locus i.coborderRange).ι) ≫ C.pD := by
      have e1 : pullback.fst (φq C hEq hW) (C.pDl i.coborderRange) ≫ φq C hEq hW =
          pullback.snd (φq C hEq hW) (C.pDl i.coborderRange) ≫ C.pDl i.coborderRange :=
        pullback.condition
      have e2 := congrArg (· ≫ (C.locus i.coborderRange).ι) e1
      simpa only [Category.assoc, φl_ι, morphismRestrict_ι] using e2
    obtain ⟨c, -, hct⟩ := exists_factor C hEq hW _ _ hab
    have he : (c ≫ t) ≫ Γq C hEq hW =
        pullback.snd (φq C hEq hW) (C.pDl i.coborderRange) := by
      rw [← cancel_mono (C.pD ⁻¹ᵁ C.locus i.coborderRange).ι, Category.assoc, graphl_ι,
        Category.assoc, hct]
    rw [← he]
    exact Scheme.Hom.le_ker_comp _ _

/-- **The relation is the fibre of the universal family**: `Z = D'' ×_{H''} Q`. -/
theorem isPullback_Γq_π [QuasiCompact p] :
    IsPullback (Γq C hEq hW) (π C hEq hW) (C.pDl i.coborderRange) (ιQ C hEq hW) := by
  have := quasiCompact_φq C hEq hW
  refine isPullback_of_isClosedImmersion _ _ _ _ ?_ ?_
  · rw [graphl_pDl, Scheme.Hom.toImage_imageι]
  · rw [Scheme.IdealSheafData.ker_subschemeι,
      KernelFlatBaseChange.ker_comap_of_flat (φq C hEq hW) (C.pDl i.coborderRange),
      ker_pullback_snd]

theorem flat_π [QuasiCompact p] : Flat (π C hEq hW) :=
  MorphismProperty.of_isPullback (isPullback_Γq_π C hEq hW) inferInstance

theorem isProper_π [QuasiCompact p] : IsProper (π C hEq hW) :=
  MorphismProperty.of_isPullback (isPullback_Γq_π C hEq hW) inferInstance

theorem locallyOfFinitePresentation_π [QuasiCompact p] :
    LocallyOfFinitePresentation (π C hEq hW) :=
  MorphismProperty.of_isPullback (isPullback_Γq_π C hEq hW) inferInstance

theorem surjective_π [QuasiCompact p] : Surjective (π C hEq hW) := by
  have := quasiCompact_φq C hEq hW
  have := isProper_π C hEq hW
  infer_instance

omit [IsSeparated C.πH] in
theorem π_ι_ι : π C hEq hW ≫ ιQ C hEq hW ≫ (C.locus i.coborderRange).ι = φ := by
  rw [Scheme.Hom.toImage_imageι_assoc, φl_ι]

omit [IsSeparated C.πH] in
theorem comp_π_eq_iff {T : Scheme.{u}} (x y : T ⟶ Z) :
    x ≫ π C hEq hW = y ≫ π C hEq hW ↔ Rel s t x y := by
  rw [rel_iff C hEq hW]
  have e := π_ι_ι C hEq hW
  constructor
  · intro hxy
    have h1 : x ≫ φ = x ≫ π C hEq hW ≫ ιQ C hEq hW ≫ (C.locus i.coborderRange).ι := by
      rw [e]
    have h2 : y ≫ φ = y ≫ π C hEq hW ≫ ιQ C hEq hW ≫ (C.locus i.coborderRange).ι := by
      rw [e]
    rw [h1, h2, reassoc_of% hxy]
  · intro hxy
    rw [← cancel_mono (ιQ C hEq hW ≫ (C.locus i.coborderRange).ι), Category.assoc,
      Category.assoc, e, hxy]

omit [IsSeparated C.πH] in
/-- **`R` is the fibre product `Z ×_Q Z`.** -/
theorem isPullback_s_t [Mono (pullback.lift s t h)] :
    IsPullback s t (π C hEq hW) (π C hEq hW) := by
  have hst : s ≫ π C hEq hW = t ≫ π C hEq hW :=
    (comp_π_eq_iff C hEq hW s t).mpr ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
  refine IsPullback.of_isLimit' ⟨hst⟩ (PullbackCone.IsLimit.mk hst
    (fun c => ((comp_π_eq_iff C hEq hW c.fst c.snd).mp c.condition).choose)
    (fun c => ((comp_π_eq_iff C hEq hW c.fst c.snd).mp c.condition).choose_spec.1)
    (fun c => ((comp_π_eq_iff C hEq hW c.fst c.snd).mp c.condition).choose_spec.2) ?_)
  intro c m hm1 hm2
  have hc := ((comp_π_eq_iff C hEq hW c.fst c.snd).mp c.condition).choose_spec
  rw [← cancel_mono (pullback.lift s t h)]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [hm1, hc.1]
  · simp only [Category.assoc, pullback.lift_snd]
    rw [hm2, hc.2]

end Quotient

end Langlands.AlgebraicGeometry.FlatEquivalenceRelation
