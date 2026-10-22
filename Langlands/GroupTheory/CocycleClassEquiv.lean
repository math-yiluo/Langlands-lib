import Langlands.GroupTheory.CocycleCohomology

/-! # Cochains and extension equivalences from equal second cohomology classes -/

noncomputable section

namespace Langlands.NormalizedTwoCocycle

universe u

variable {G A : Type u} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- Equal actual classes give a cochain `b` with `c(g,h) b(gh) = b(g) (g • b(h)) d(g,h)`. -/
theorem exists_cochain_of_cohomologyClass_eq {c d : NormalizedTwoCocycle G A}
    (hcd : cohomologyClass c = cohomologyClass d) :
    ∃ b : G → A, ∀ g h, c (g, h) * b (g * h) = b g * (g • b h) * d (g, h) := by
  obtain ⟨x, hx⟩ := (groupCohomology.H2π_eq_iff (toCocycle₂ c) (toCocycle₂ d)).1 hcd
  refine ⟨fun g => @Additive.toMul A (x g), fun g h => ?_⟩
  have he : (g • @Additive.toMul A (x h)) / @Additive.toMul A (x (g * h)) *
      @Additive.toMul A (x g) = c (g, h) / d (g, h) :=
    congrArg Additive.toMul (congrFun hx (g, h))
  rw [eq_div_iff_mul_eq'] at he
  rw [← he]
  simp only [div_eq_mul_inv]
  calc
    _ = (g • @Additive.toMul A (x h)) * @Additive.toMul A (x g) * d (g, h) *
        ((@Additive.toMul A (x (g * h)))⁻¹ * @Additive.toMul A (x (g * h))) := by ac_rfl
    _ = _ := by rw [inv_mul_cancel, mul_one]; ac_rfl

/-- Equality of actual classes is exactly the existence of a relating cochain. -/
theorem cohomologyClass_eq_iff_exists_cochain (c d : NormalizedTwoCocycle G A) :
    cohomologyClass c = cohomologyClass d ↔
      ∃ b : G → A, ∀ g h, c (g, h) * b (g * h) = b g * (g • b h) * d (g, h) :=
  ⟨exists_cochain_of_cohomologyClass_eq,
    fun ⟨b, hb⟩ => cohomologyClass_eq_of_cochain c d b hb⟩

/-- A cochain chosen from equality of classes; it is not unique. -/
def classCochain {c d : NormalizedTwoCocycle G A}
    (hcd : cohomologyClass c = cohomologyClass d) : G → A :=
  (exists_cochain_of_cohomologyClass_eq hcd).choose

theorem classCochain_spec {c d : NormalizedTwoCocycle G A}
    (hcd : cohomologyClass c = cohomologyClass d) (g h : G) :
    c (g, h) * classCochain hcd (g * h) =
      classCochain hcd g * (g • classCochain hcd h) * d (g, h) :=
  (exists_cochain_of_cohomologyClass_eq hcd).choose_spec g h

namespace MapData

/-- Identity-component map data whose cochain is the chosen `classCochain`. -/
def ofCohomologyClassEq {c d : NormalizedTwoCocycle G A}
    (hcd : cohomologyClass c = cohomologyClass d) :
    MapData c d (MonoidHom.id A) (MonoidHom.id G) where
  cochain := classCochain hcd
  equivariant _ _ := rfl
  compatible := classCochain_spec hcd

@[simp] theorem ofCohomologyClassEq_cochain {c d : NormalizedTwoCocycle G A}
    (hcd : cohomologyClass c = cohomologyClass d) :
    (ofCohomologyClassEq hcd).cochain = classCochain hcd := rfl

end MapData

section Topology

variable [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace A] [IsTopologicalGroup A]

/-- Over a discrete acting group, equal classes give a continuous extension equivalence. -/
def continuousEquivOfCohomologyClassEq {c d : NormalizedTwoCocycle G A}
    (hcd : cohomologyClass c = cohomologyClass d) : c.Extension ≃ₜ* d.Extension :=
  MapData.continuousEquivOfEquivs (ContinuousMulEquiv.refl A) (ContinuousMulEquiv.refl G)
    (MapData.ofCohomologyClassEq hcd) continuous_of_discreteTopology

variable {c d : NormalizedTwoCocycle G A} (hcd : cohomologyClass c = cohomologyClass d)

theorem continuousEquivOfCohomologyClassEq_apply (t : c.Extension) :
    continuousEquivOfCohomologyClassEq hcd t =
      (MapData.ofCohomologyClassEq hcd).toMonoidHom t := rfl

@[simp] theorem continuousEquivOfCohomologyClassEq_left (t : c.Extension) :
    (continuousEquivOfCohomologyClassEq hcd t).left = t.left * classCochain hcd t.right :=
  rfl

@[simp] theorem continuousEquivOfCohomologyClassEq_right (t : c.Extension) :
    (continuousEquivOfCohomologyClassEq hcd t).right = t.right := rfl

theorem continuousEquivOfCohomologyClassEq_symm_apply (t : d.Extension) :
    (continuousEquivOfCohomologyClassEq hcd).symm t =
      ⟨t.left / classCochain hcd t.right, t.right⟩ := rfl

@[simp] theorem continuousEquivOfCohomologyClassEq_inl (a : A) :
    continuousEquivOfCohomologyClassEq hcd (Extension.inl c a) = Extension.inl d a :=
  (MapData.ofCohomologyClassEq hcd).toMonoidHom_inl a

@[simp] theorem projection_continuousEquivOfCohomologyClassEq (t : c.Extension) :
    Extension.projection d (continuousEquivOfCohomologyClassEq hcd t) =
      Extension.projection c t := rfl

@[simp] theorem continuousEquivOfCohomologyClassEq_symm_inl (a : A) :
    (continuousEquivOfCohomologyClassEq hcd).symm (Extension.inl d a) = Extension.inl c a := by
  rw [ContinuousMulEquiv.symm_apply_eq, continuousEquivOfCohomologyClassEq_inl]

@[simp] theorem projection_continuousEquivOfCohomologyClassEq_symm (t : d.Extension) :
    Extension.projection c ((continuousEquivOfCohomologyClassEq hcd).symm t) =
      Extension.projection d t := rfl

end Topology

end Langlands.NormalizedTwoCocycle
