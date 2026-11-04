import Langlands.Representation.Induction.SmoothSplitQuotient

/-!
# Restriction of smooth induction to an open subgroup

When `G = P K` with `K` open, restriction identifies actual smooth induction
from `P` with smooth induction on `K` from its actual intersection with `P`.
The inverse is extension by covariance, with its global smoothness proved.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (P : Subgroup G) (K : OpenSubgroup G) (σ : Representation R P V)

/-- The actual inducing action on `P ∩ K`, viewed as a subgroup of `K`. -/
abbrev openSubgroupInducingRepresentation :
    Representation R (P.comap K.toSubgroup.subtype) V :=
  σ.comp (K.toSubgroup.subtype.subgroupComap P)

/-- Restrict an actual smooth induced function to the open subgroup. -/
def openSubgroupInductionRestrict
    (f : SmoothFunctions P σ) :
    SmoothFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ) :=
  smoothSplitQuotientRestrict K.toSubgroup.subtype continuous_subtype_val P σ f

omit [IsTopologicalGroup G] in
@[simp]
theorem openSubgroupInductionRestrict_eval (f : SmoothFunctions P σ) (k : K) :
    eval _ _ (openSubgroupInductionRestrict P K σ f) k = eval P σ f k := rfl

omit [IsTopologicalGroup G] in
private theorem factorization_value
    (f : EquivariantFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ))
    (p q : P) (k l : K) (he : (p : G) * (k : G) = (q : G) * (l : G)) :
    σ p (f.1 k) = σ q (f.1 l) := by
  have he' : (q : G)⁻¹ * (p : G) = (l : G) * (k : G)⁻¹ := by
    simpa [mul_assoc] using
      congrArg (fun x : G => (q : G)⁻¹ * x * (k : G)⁻¹) he
  let a : P.comap K.toSubgroup.subtype :=
    ⟨l * k⁻¹, by
      change (l : G) * (k : G)⁻¹ ∈ P
      rw [← he']
      exact P.mul_mem (P.inv_mem q.property) p.property⟩
  have ha : K.toSubgroup.subtype.subgroupComap P a = q⁻¹ * p :=
    Subtype.ext he'.symm
  have hf := f.property a k
  change f.1 ((l * k⁻¹) * k) =
    σ (K.toSubgroup.subtype.subgroupComap P a) (f.1 k) at hf
  rw [inv_mul_cancel_right, ha] at hf
  rw [hf, map_mul]
  change σ p (f.1 k) = σ q (σ (q⁻¹) (σ p (f.1 k)))
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

variable (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

private def extensionValue
    (f : SmoothFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ)) (g : G) : V :=
  σ (hPK g).choose (eval _ _ f (hPK g).choose_spec.choose)

omit [IsTopologicalGroup G] in
private theorem extensionValue_mul
    (f : SmoothFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ)) (p : P) (k : K) :
    extensionValue P K σ hPK f ((p : G) * (k : G)) = σ p (eval _ _ f k) :=
  factorization_value P K σ f.1 _ p _ k
    (hPK ((p : G) * (k : G))).choose_spec.choose_spec.symm

private def imageOpenSubgroup (H : OpenSubgroup K) : OpenSubgroup G :=
  ⟨H.toSubgroup.map K.toSubgroup.subtype,
    K.isOpen.isOpenMap_subtype_val _ H.isOpen⟩

/-- Extend a smooth section on the actual intersection by its covariance.
The factorization hypothesis is data about the two actual subgroups. -/
def openSubgroupInductionExtend
    (f : SmoothFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ)) : SmoothFunctions P σ := by
  let H := Classical.choose f.property
  have hH := Classical.choose_spec f.property
  refine smoothFunctionOf P σ (extensionValue P K σ hPK f) ?_
    (imageOpenSubgroup K H) ?_
  · intro p x
    obtain ⟨q, k, rfl⟩ := hPK x
    have he : (p : G) * ((q : G) * (k : G)) = ((p * q : P) : G) * (k : G) :=
      (mul_assoc _ _ _).symm
    rw [he, extensionValue_mul, extensionValue_mul, map_mul]
    rfl
  · intro y x
    obtain ⟨k, hk, he⟩ := y.property
    obtain ⟨p, l, rfl⟩ := hPK x
    have hfl : eval _ _ f (l * k) = eval _ _ f l :=
      congrArg (fun F : EquivariantFunctions (P.comap K.toSubgroup.subtype)
        (openSubgroupInducingRepresentation P K σ) => F.1 l) (hH ⟨k, hk⟩)
    change extensionValue P K σ hPK f ((p : G) * (l : G) * (y : G)) =
      extensionValue P K σ hPK f ((p : G) * (l : G))
    rw [← he, mul_assoc]
    change extensionValue P K σ hPK f ((p : G) * ((l * k : K) : G)) =
      extensionValue P K σ hPK f ((p : G) * (l : G))
    rw [extensionValue_mul, extensionValue_mul, hfl]

omit [IsTopologicalGroup G] in
/-- The extension at any factorization is independent of the chosen
factorization used in its construction. -/
@[simp]
theorem openSubgroupInductionExtend_mul
    (f : SmoothFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ)) (p : P) (k : K) :
    eval P σ (openSubgroupInductionExtend P K σ hPK f) ((p : G) * (k : G)) =
      σ p (eval _ _ f k) :=
  extensionValue_mul P K σ hPK f p k

/-- Restriction is an equivalence for the actual right `K` actions when
every element of `G` factors as an element of `P` followed by one of `K`. -/
def openSubgroupInductionEquiv :
    Representation.Equiv ((smoothInduced P σ).comp K.toSubgroup.subtype)
      (smoothInduced (P.comap K.toSubgroup.subtype)
        (openSubgroupInducingRepresentation P K σ)) where
  toLinearMap :=
    { toFun := openSubgroupInductionRestrict P K σ
      map_add' f g := by
        apply Subtype.ext
        apply Subtype.ext
        funext k
        rfl
      map_smul' c f := by
        apply Subtype.ext
        apply Subtype.ext
        funext k
        rfl }
  invFun := openSubgroupInductionExtend P K σ hPK
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    obtain ⟨p, k, rfl⟩ := hPK x
    exact (openSubgroupInductionExtend_mul P K σ hPK _ p k).trans
      (f.1.property p k).symm
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change eval P σ (openSubgroupInductionExtend P K σ hPK f) (k : G) = eval _ _ f k
    have he := openSubgroupInductionExtend_mul P K σ hPK f 1 k
    simpa only [OneMemClass.coe_one, one_mul, map_one, Module.End.one_apply] using he
  isIntertwining' k := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext l
    rfl

@[simp]
theorem openSubgroupInductionEquiv_eval (f : SmoothFunctions P σ) (k : K) :
    eval _ _ (openSubgroupInductionEquiv P K σ hPK f) k = eval P σ f k := rfl

@[simp]
theorem openSubgroupInductionEquiv_symm_mul
    (f : SmoothFunctions (P.comap K.toSubgroup.subtype)
      (openSubgroupInducingRepresentation P K σ)) (p : P) (k : K) :
    eval P σ ((openSubgroupInductionEquiv P K σ hPK).symm f)
        ((p : G) * (k : G)) = σ p (eval _ _ f k) :=
  openSubgroupInductionExtend_mul P K σ hPK f p k

variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The restriction equivalence commutes with actual coefficient intertwiners
and permits independent coefficient-carrier universes. -/
theorem openSubgroupInductionEquiv_natural (τ : Representation R P W)
    (T : σ.IntertwiningMap τ) (f : SmoothFunctions P σ) :
    openSubgroupInductionEquiv P K τ hPK (smoothInducedMap P T f) =
      smoothInducedMap (P.comap K.toSubgroup.subtype)
        (restrictAlongMap (K.toSubgroup.subtype.subgroupComap P) T)
        (openSubgroupInductionEquiv P K σ hPK f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

end Langlands.Induction
