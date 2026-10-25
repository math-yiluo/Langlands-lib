import Langlands.Representation.Induction.StructuralStatement

/-! # Scalar character twists of smooth and compact induction -/

noncomputable section

namespace Langlands.Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable [IsTopologicalGroup G]

private def smoothTwistTo (H : Subgroup G) (chi : SmoothCharacter ℂ G)
    (sigma : Representation ℂ H V) (f : SmoothFunctions H sigma) :
    SmoothFunctions H (twist (chi.toMonoidHom.comp H.subtype) sigma) := by
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine smoothFunctionOf H _ (fun x => (chi.toMonoidHom x : ℂ) • eval H sigma f x)
    ?_ (K ⊓ ⟨chi.toMonoidHom.ker, chi.isOpen_ker⟩) ?_
  · intro h x
    have hf : f.1.1 ((h : G) * x) = sigma h (f.1.1 x) := f.1.property h x
    change (chi.toMonoidHom ((h : G) * x) : ℂ) • f.1.1 ((h : G) * x) =
      (chi.toMonoidHom (h : G) : ℂ) • sigma h ((chi.toMonoidHom x : ℂ) • f.1.1 x)
    rw [hf]
    simp only [map_mul, Units.val_mul, map_smul, mul_smul]
  · intro k x
    have hk : chi.toMonoidHom (k : G) = 1 := k.property.2
    have hf := congrArg (fun F : EquivariantFunctions H sigma => F.1 x)
      (hK ⟨(k : G), k.property.1⟩)
    change eval H sigma f (x * (k : G)) = eval H sigma f x at hf
    simp only [map_mul, hk, mul_one, hf]

private def smoothTwistFrom (H : Subgroup G) (chi : SmoothCharacter ℂ G)
    (sigma : Representation ℂ H V)
    (f : SmoothFunctions H (twist (chi.toMonoidHom.comp H.subtype) sigma)) :
    SmoothFunctions H sigma := by
  let K := Classical.choose f.property
  have hK := Classical.choose_spec f.property
  refine smoothFunctionOf H sigma
    (fun x => ((chi.toMonoidHom x)⁻¹ : ℂˣ) •
      eval H (twist (chi.toMonoidHom.comp H.subtype) sigma) f x)
    ?_ (K ⊓ ⟨chi.toMonoidHom.ker, chi.isOpen_ker⟩) ?_
  · intro h x
    have hf := f.1.property h x
    change f.1.1 ((h : G) * x) =
      (chi.toMonoidHom (h : G) : ℂ) • sigma h (f.1.1 x) at hf
    change ((chi.toMonoidHom ((h : G) * x))⁻¹ : ℂˣ) • f.1.1 ((h : G) * x) =
      sigma h (((chi.toMonoidHom x)⁻¹ : ℂˣ) • f.1.1 x)
    simp only [Units.smul_def] at *
    rw [hf, map_smul, smul_smul]
    congr 1
    rw [← Units.val_mul, map_mul, mul_inv_rev]
    simp [mul_assoc]
  · intro k x
    have hk : chi.toMonoidHom (k : G) = 1 := k.property.2
    have hf := congrArg
      (fun F : EquivariantFunctions H
        (twist (chi.toMonoidHom.comp H.subtype) sigma) => F.1 x)
      (hK ⟨(k : G), k.property.1⟩)
    change eval H _ f (x * (k : G)) = eval H _ f x at hf
    simp only [map_mul, hk, mul_one, hf]

/-- Multiplication by the character on the actual smooth induced functions. -/
def smoothInductionTwistEquiv (H : Subgroup G) (chi : SmoothCharacter ℂ G)
    (sigma : Representation ℂ H V) :
    (twist chi.toMonoidHom (smoothInduced H sigma)).Equiv
      (smoothInduced H (twist (chi.toMonoidHom.comp H.subtype) sigma)) where
  toLinearMap :=
    { toFun := smoothTwistTo H chi sigma
      map_add' f g := by
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change (chi.toMonoidHom x : ℂ) • (eval H sigma f x + eval H sigma g x) =
          (chi.toMonoidHom x : ℂ) • eval H sigma f x +
            (chi.toMonoidHom x : ℂ) • eval H sigma g x
        exact smul_add _ _ _
      map_smul' c f := by
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change (chi.toMonoidHom x : ℂ) • (c • eval H sigma f x) =
          c • ((chi.toMonoidHom x : ℂ) • eval H sigma f x)
        exact smul_comm _ _ _ }
  invFun := smoothTwistFrom H chi sigma
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change ((chi.toMonoidHom x)⁻¹ : ℂˣ) •
      ((chi.toMonoidHom x : ℂ) • eval H sigma f x) = eval H sigma f x
    simp [Units.smul_def, smul_smul]
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (chi.toMonoidHom x : ℂ) •
      (((chi.toMonoidHom x)⁻¹ : ℂˣ) • eval H _ f x) = eval H _ f x
    simp [Units.smul_def, smul_smul]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (chi.toMonoidHom x : ℂ) •
      ((chi.toMonoidHom g : ℂ) • eval H sigma f (x * g)) =
        (chi.toMonoidHom (x * g) : ℂ) • eval H sigma f (x * g)
    simp only [map_mul, Units.val_mul, mul_smul]

@[simp]
theorem smoothInductionTwistEquiv_eval (H : Subgroup G) (chi : SmoothCharacter ℂ G)
    (sigma : Representation ℂ H V) (f : SmoothFunctions H sigma) (x : G) :
    eval H (twist (chi.toMonoidHom.comp H.subtype) sigma)
      (smoothInductionTwistEquiv H chi sigma f) x =
        (chi.toMonoidHom x : ℂ) • eval H sigma f x := rfl

@[simp]
theorem smoothInductionTwistEquiv_symm_eval (H : Subgroup G)
    (chi : SmoothCharacter ℂ G) (sigma : Representation ℂ H V)
    (f : SmoothFunctions H (twist (chi.toMonoidHom.comp H.subtype) sigma)) (x : G) :
    eval H sigma ((smoothInductionTwistEquiv H chi sigma).symm f) x =
      ((chi.toMonoidHom x)⁻¹ : ℂˣ) •
        eval H (twist (chi.toMonoidHom.comp H.subtype) sigma) f x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Multiplication by unit-valued scalars preserves the exact projected nonzero support. -/
theorem quotientSupport_unit_smul (H : Subgroup G) (c : G → ℂˣ) (f : G → V) :
    quotientSupport H (fun x => (c x : ℂ) • f x) = quotientSupport H f := by
  unfold quotientSupport
  congr 1
  ext x
  change (c x) • f x ≠ 0 ↔ f x ≠ 0
  exact smul_ne_zero_iff_ne (c x)

theorem smoothInductionTwistEquiv_quotientSupport (H : Subgroup G)
    (chi : SmoothCharacter ℂ G) (sigma : Representation ℂ H V)
    (f : SmoothFunctions H sigma) :
    quotientSupport H (eval H _ (smoothInductionTwistEquiv H chi sigma f)) =
      quotientSupport H (eval H sigma f) :=
  quotientSupport_unit_smul H chi.toMonoidHom (eval H sigma f)

theorem smoothInductionTwistEquiv_symm_quotientSupport (H : Subgroup G)
    (chi : SmoothCharacter ℂ G) (sigma : Representation ℂ H V)
    (f : SmoothFunctions H (twist (chi.toMonoidHom.comp H.subtype) sigma)) :
    quotientSupport H (eval H sigma ((smoothInductionTwistEquiv H chi sigma).symm f)) =
      quotientSupport H (eval H _ f) :=
  quotientSupport_unit_smul H (fun x => (chi.toMonoidHom x)⁻¹) (eval H _ f)

/-- Restriction of the same character multiplication to actual compact induction. -/
def compactInductionTwistEquiv (H : Subgroup G) (chi : SmoothCharacter ℂ G)
    (sigma : Representation ℂ H V) :
    (twist chi.toMonoidHom (compactInduced H sigma)).Equiv
      (compactInduced H (twist (chi.toMonoidHom.comp H.subtype) sigma)) where
  toLinearMap :=
    { toFun f := ⟨smoothInductionTwistEquiv H chi sigma f.1, by
        change IsCompact (quotientSupport H
          (eval H _ (smoothInductionTwistEquiv H chi sigma f.1)))
        rw [smoothInductionTwistEquiv_quotientSupport]
        exact f.property⟩
      map_add' f g := by
        apply Subtype.ext
        exact (smoothInductionTwistEquiv H chi sigma).map_add f.1 g.1
      map_smul' c f := by
        apply Subtype.ext
        exact (smoothInductionTwistEquiv H chi sigma).map_smul c f.1 }
  invFun f := ⟨(smoothInductionTwistEquiv H chi sigma).symm f.1, by
    change IsCompact (quotientSupport H
      (eval H sigma ((smoothInductionTwistEquiv H chi sigma).symm f.1)))
    rw [smoothInductionTwistEquiv_symm_quotientSupport]
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (smoothInductionTwistEquiv H chi sigma).symm_apply_apply f.1
  right_inv f := by
    apply Subtype.ext
    exact (smoothInductionTwistEquiv H chi sigma).apply_symm_apply f.1
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun m : SmoothFunctions H sigma →ₗ[ℂ]
      SmoothFunctions H (twist (chi.toMonoidHom.comp H.subtype) sigma) => m f.1)
      ((smoothInductionTwistEquiv H chi sigma).isIntertwining' g)

@[simp]
theorem compactInductionTwistEquiv_eval (H : Subgroup G) (chi : SmoothCharacter ℂ G)
    (sigma : Representation ℂ H V) (f : CompactFunctions H sigma) (x : G) :
    eval H (twist (chi.toMonoidHom.comp H.subtype) sigma)
      (compactInductionTwistEquiv H chi sigma f).1 x =
        (chi.toMonoidHom x : ℂ) • eval H sigma f.1 x := rfl

/-- Smooth and compact induction commute with scalar character twists. -/
theorem inductionTwist (H : Subgroup G) : InductionTwistClause (V := V) H := by
  intro chi sigma _hsigma
  exact ⟨⟨smoothInductionTwistEquiv H chi sigma, fun _ _ => rfl⟩,
    ⟨compactInductionTwistEquiv H chi sigma, fun _ _ => rfl⟩⟩

end Langlands.Induction
