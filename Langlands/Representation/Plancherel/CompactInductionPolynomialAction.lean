import Langlands.Representation.Plancherel.CompactInductionGeneration

/-! # Polynomial actual normalized-induction actions on the compact picture -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

local instance compactPolynomialActionTopologicalGroup : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup K.toSubgroup)

/-- Bundle the existing actual parameter translates as a representation of
the whole ambient group on the fixed compact carrier. -/
def unramifiedCompactRepresentation (χ : unramifiedCharacters ν) :
    Representation ℂ G (CompactInductionPicture h K A) where
  toFun := compactTranslate h hU hδ K hP hK hPK ν hν hr A χ
  map_one' := by
    apply LinearMap.ext
    intro f
    simp only [compactTranslate, map_one, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' := compactTranslate_mul h hU hδ K hP hK hPK ν hν hr A χ

/-- Restriction and normalized covariance extension give an equivalence for
the full ambient actions, rather than only their compact restrictions. -/
def unramifiedCompactRepresentationEquiv (χ : unramifiedCharacters ν) :
    (UnramifiedLeviInduction h hU ν χ A).representation.Equiv
      (unramifiedCompactRepresentation h hU hδ K hP hK hPK ν hν hr A χ) :=
  Representation.Equiv.mk
    (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A)
    (fun g => by
      apply LinearMap.ext
      intro f
      change
        (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A)
            ((UnramifiedLeviInduction h hU ν χ A).representation g f) =
          compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g
            ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A) f)
      simp only [compactTranslate, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

/-- The constructed full action restricts to the original fixed right action
on the compact subgroup, independently of the parameter. -/
theorem unramifiedCompactRepresentation_comp (χ : unramifiedCharacters ν) :
    (unramifiedCompactRepresentation h hU hδ K hP hK hPK ν hν hr A χ).comp
        K.toSubgroup.subtype =
      compactPictureAction h K A := by
  apply MonoidHom.ext
  intro k
  exact compactTranslate_of_mem h hU hδ K hP hK hPK ν hν hr A χ k

/-- The transported ambient representation is smooth. -/
theorem unramifiedCompactRepresentation_isSmooth (χ : unramifiedCharacters ν) :
    IsSmooth (unramifiedCompactRepresentation h hU hδ K hP hK hPK ν hν hr A χ) := by
  intro f
  let E := unramifiedCompactRepresentationEquiv h hU hδ K hP hK hPK ν hν hr A χ
  obtain ⟨H, hH⟩ := (UnramifiedLeviInduction h hU ν χ A).isSmooth (E.symm f)
  refine ⟨H, fun x => ?_⟩
  have he := congrArg E (hH x)
  have ht := E.toIntertwiningMap.isIntertwining
    (UnramifiedLeviInduction h hU ν χ A).representation
    (unramifiedCompactRepresentation h hU hδ K hP hK hPK ν hν hr A χ) x.val (E.symm f)
  change E ((UnramifiedLeviInduction h hU ν χ A).representation x.val (E.symm f)) =
    E (E.symm f) at he
  change E ((UnramifiedLeviInduction h hU ν χ A).representation x.val (E.symm f)) =
    unramifiedCompactRepresentation h hU hδ K hP hK hPK ν hν hr A χ x.val
      (E (E.symm f)) at ht
  rw [Representation.Equiv.apply_symm_apply] at he ht
  exact ht.symm.trans he

omit [LocallyCompactSpace G] in
/-- Every compact section has one ambient open stabilizer contained in `K`;
it is therefore usable at all unramified parameters. -/
theorem exists_compactPicture_stabilizer (f : CompactInductionPicture h K A) :
    ∃ H : OpenSubgroup G, H ≤ K ∧
      f ∈ fixedVectors (compactPictureAction h K A) (compactFixedSubgroup K H) := by
  obtain ⟨J, hJ⟩ := smoothInduced_smooth (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A) f
  let H : OpenSubgroup G :=
    ⟨J.toSubgroup.map K.toSubgroup.subtype,
      K.isOpen.isOpenMap_subtype_val _ J.isOpen⟩
  have hHK : H ≤ K := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  refine ⟨H, hHK, ?_⟩
  intro x
  obtain ⟨y, hy, he⟩ := x.property
  have hey : y = x.val := Subtype.ext he
  change compactPictureAction h K A x.val f = f
  rw [← hey]
  exact hJ ⟨y, hy⟩

/-- Conjugating a common open stabilizer gives a common stabilizer for all
parameter translates. -/
theorem compactTranslate_mem_compactFixed (χ : unramifiedCharacters ν) (g : G)
    (H L : OpenSubgroup G) (hHK : H ≤ K)
    (hconj : ∀ x : G, x ∈ L → g⁻¹ * x * g ∈ H)
    (w : CompactFixedVectors h K A H) :
    compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g w.val ∈
      fixedVectors (compactPictureAction h K A) (compactFixedSubgroup K L) := by
  intro x
  have hm : g⁻¹ * (x.val : G) * g ∈ H := hconj _ x.property
  let y : K := ⟨g⁻¹ * (x.val : G) * g, hHK hm⟩
  have hfix : compactTranslate h hU hδ K hP hK hPK ν hν hr A χ
      (g⁻¹ * (x.val : G) * g) w.val = w.val := by
    rw [show g⁻¹ * (x.val : G) * g = (y : G) from rfl,
      compactTranslate_of_mem]
    exact w.property ⟨y, hm⟩
  change compactPictureAction h K A x.val
    (compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g w.val) = _
  rw [← compactTranslate_of_mem h hU hδ K hP hK hPK ν hν hr A χ x.val,
    ← Module.End.mul_apply, ← compactTranslate_mul]
  have he : (x.val : G) * g = g * (g⁻¹ * (x.val : G) * g) := by simp [mul_assoc]
  rw [he, compactTranslate_mul, Module.End.mul_apply, hfix]

/-- Each actual ambient action operator is polynomial in the unramified
parameter, on any parameter subset. No admissibility is required. -/
theorem isPolynomialOperatorOn_compactTranslate (g : G)
    (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOperatorOn Ω
      (fun χ => compactTranslate h hU hδ K hP hK hPK ν hν hr A χ.val g) := by
  intro f
  obtain ⟨H, hHK, hf⟩ := exists_compactPicture_stabilizer h K A f
  let L : OpenSubgroup G :=
    K ⊓ H.comap (MulAut.conj g⁻¹).toMonoidHom
      (IsTopologicalGroup.continuous_conj g⁻¹)
  have hconj : ∀ x : G, x ∈ L → g⁻¹ * x * g ∈ H := by
    intro x hx
    have hxH := hx.2
    change g⁻¹ * x * g⁻¹⁻¹ ∈ H at hxH
    simpa only [inv_inv] using hxH
  let X : Ω → CompactFixedVectors h K A L := fun χ =>
    ⟨compactTranslate h hU hδ K hP hK hPK ν hν hr A χ.val g f,
      compactTranslate_mem_compactFixed h hU hδ K hP hK hPK ν hν hr A
        χ.val g H L hHK hconj ⟨f, hf⟩⟩
  have hX : IsPolynomialOn Ω X := by
    apply isPolynomialOn_compactFixed_of_eval h K hK ν A L
    intro k
    change IsPolynomialOn Ω (fun χ =>
      eval _ _ (compactTranslate h hU hδ K hP hK hPK ν hν hr A χ.val g f) k)
    simp_rw [eval_compactTranslate]
    exact unramifiedCompactExtension_eval_isPolynomialOn h hU hδ K hP hK hPK
      ν hν hr A Ω f ((k : G) * g)
  exact hX.linearMap (Submodule.subtype _)

/-- Polynomiality of the constructed full compact-picture representation
family, with the exact operator predicate needed for rational continuation. -/
theorem unramifiedCompactRepresentation_polynomial (g : G)
    (Ω : Set (unramifiedCharacters ν)) :
    IsPolynomialOperatorOn Ω
      (fun χ => unramifiedCompactRepresentation h hU hδ K hP hK hPK ν hν hr A χ.val g) :=
  isPolynomialOperatorOn_compactTranslate h hU hδ K hP hK hPK ν hν hr A g Ω

end Langlands.Plancherel
