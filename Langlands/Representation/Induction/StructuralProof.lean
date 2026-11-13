import Langlands.Representation.Induction.StructuralStatement
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.SmoothTransitivity
import Langlands.Representation.Induction.CompactTransitivityProof
import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Induction.CompactSurjectivityProof

/-!
# Structural properties of smooth and compact induction

Proof of `Langlands.Induction.StructuralStatement` (Renard III.2.2–III.2.8): Frobenius
reciprocity, exactness, the compact-quotient clause, character twists, central actions,
induction in stages and the open-subgroup adjunction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uG uU uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

section Clauses

variable [IsTopologicalGroup G] (H : Subgroup G)

omit [IsTopologicalGroup G] in
/-- Smooth induced functions are determined by their values. -/
theorem structural_smooth_ext {sigma : Representation ℂ H V} {f f' : SmoothFunctions H sigma}
    (he : ∀ x, eval H sigma f x = eval H sigma f' x) : f = f' :=
  Subtype.ext (Subtype.ext (funext he))

/-! ### Frobenius reciprocity -/

section Frobenius

variable (rho : Representation ℂ G U) (sigma : Representation ℂ H V)

/-- The smooth induced function `x ↦ φ (rho x u)` attached to an `H`-intertwiner `φ`. -/
def frobeniusFunction (hrho : IsSmooth rho)
    (φ : Representation.IntertwiningMap (rho.comp H.subtype) sigma) (u : U) : SmoothFunctions H sigma :=
  smoothFunctionOf H sigma (fun x => φ (rho x u))
    (by
      intro h x
      change φ (rho ((h : G) * x) u) = sigma h (φ (rho x u))
      rw [map_mul, Module.End.mul_apply]
      exact Representation.IntertwiningMap.isIntertwining _ _ φ h (rho x u))
    (Classical.choose (hrho u))
    (by
      intro k x
      have hk : rho (k : G) u = u := Classical.choose_spec (hrho u) ⟨k.1, k.2⟩
      change φ (rho (x * (k : G)) u) = φ (rho x u)
      rw [map_mul, Module.End.mul_apply, hk])

omit [IsTopologicalGroup G] in
theorem eval_frobeniusFunction (hrho : IsSmooth rho)
    (φ : Representation.IntertwiningMap (rho.comp H.subtype) sigma) (u : U) (x : G) :
    eval H sigma (frobeniusFunction H rho sigma hrho φ u) x = φ (rho x u) :=
  rfl

/-- The inverse Frobenius map: an `H`-intertwiner `φ` gives `u ↦ (x ↦ φ (rho x u))`. -/
def frobeniusInverse (hrho : IsSmooth rho)
    (φ : Representation.IntertwiningMap (rho.comp H.subtype) sigma) :
    rho.IntertwiningMap (smoothInduced H sigma) where
  toFun := frobeniusFunction H rho sigma hrho φ
  map_add' u u' := structural_smooth_ext H fun x => by
    change φ (rho x (u + u')) = φ (rho x u) + φ (rho x u')
    rw [map_add, map_add]
  map_smul' c u := structural_smooth_ext H fun x => by
    change φ (rho x (c • u)) = c • φ (rho x u)
    rw [map_smul, map_smul]
  isIntertwining' g := LinearMap.ext fun u => structural_smooth_ext H fun x => by
    change φ (rho x (rho g u)) = φ (rho (x * g) u)
    rw [map_mul, Module.End.mul_apply]

/-- Evaluation at the identity of a map into smooth induction. -/
def frobeniusRestrict (f : rho.IntertwiningMap (smoothInduced H sigma)) :
    Representation.IntertwiningMap (rho.comp H.subtype) sigma where
  toFun u := eval H sigma (f u) 1
  map_add' u u' := by
    rw [map_add]
    rfl
  map_smul' c u := by
    change eval H sigma (f (c • u)) 1 = c • eval H sigma (f u) 1
    rw [map_smul]
    rfl
  isIntertwining' h := LinearMap.ext fun u => by
    change eval H sigma (f (rho (h : G) u)) 1 = sigma h (eval H sigma (f u) 1)
    rw [Representation.IntertwiningMap.isIntertwining _ _ f]
    change eval H sigma (f u) (1 * (h : G)) = sigma h (eval H sigma (f u) 1)
    rw [one_mul]
    have hcov := eval_covariant H sigma (f u) h 1
    rw [mul_one] at hcov
    exact hcov

/-- Frobenius reciprocity for smooth induction, as an actual linear equivalence. -/
def smoothFrobeniusEquiv (hrho : IsSmooth rho) :
    (rho.IntertwiningMap (smoothInduced H sigma)) ≃ₗ[ℂ]
      (Representation.IntertwiningMap (rho.comp H.subtype) sigma) where
  toFun := frobeniusRestrict H rho sigma
  invFun := frobeniusInverse H rho sigma hrho
  map_add' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  left_inv f := Representation.IntertwiningMap.ext (LinearMap.ext fun u =>
    structural_smooth_ext H fun x => by
      change eval H sigma (f (rho x u)) 1 = eval H sigma (f u) x
      rw [Representation.IntertwiningMap.isIntertwining _ _ f]
      change eval H sigma (f u) (1 * x) = eval H sigma (f u) x
      rw [one_mul])
  right_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun u => by
    change φ (rho 1 u) = φ u
    rw [map_one, Module.End.one_apply])

theorem smoothFrobeniusEquiv_apply (hrho : IsSmooth rho)
    (f : rho.IntertwiningMap (smoothInduced H sigma)) (u : U) :
    smoothFrobeniusEquiv H rho sigma hrho f u = eval H sigma (f u) 1 :=
  rfl

end Frobenius

/-- The Frobenius clause. -/
theorem smoothFrobenius : SmoothFrobeniusClause (U := U) (V := V) H := by
  intro rho sigma hrho _hsigma
  exact ⟨smoothFrobeniusEquiv H rho sigma hrho, fun f u => rfl⟩

/-! ### Exactness -/

section Exactness

variable {rho : Representation ℂ H U} {sigma : Representation ℂ H V}

/-- A smooth induced function with values in the range of an injective intertwiner `i`,
pulled back through `i`. -/
def injectiveLift (i : rho.IntertwiningMap sigma) (hi : Function.Injective i)
    (F : SmoothFunctions H sigma) (hF : ∀ x, ∃ u, i u = eval H sigma F x) :
    SmoothFunctions H rho :=
  smoothFunctionOf H rho (fun x => Classical.choose (hF x))
    (by
      intro h x
      apply hi
      change i (Classical.choose (hF ((h : G) * x))) = i (rho h (Classical.choose (hF x)))
      rw [Classical.choose_spec (hF ((h : G) * x)),
        Representation.IntertwiningMap.isIntertwining _ _ i, Classical.choose_spec (hF x)]
      exact eval_covariant H sigma F h x)
    (Classical.choose F.property)
    (by
      intro k x
      apply hi
      rw [Classical.choose_spec (hF (x * (k : G))), Classical.choose_spec (hF x)]
      exact congrArg (fun F' : EquivariantFunctions H sigma => F'.1 x)
        (Classical.choose_spec F.property ⟨k.1, k.2⟩))

omit [IsTopologicalGroup G] in
theorem injectiveLift_eval (i : rho.IntertwiningMap sigma) (hi : Function.Injective i)
    (F : SmoothFunctions H sigma) (hF : ∀ x, ∃ u, i u = eval H sigma F x) (x : G) :
    i (eval H rho (injectiveLift H i hi F hF) x) = eval H sigma F x :=
  Classical.choose_spec (hF x)

omit [IsTopologicalGroup G] in
theorem support_injectiveLift (i : rho.IntertwiningMap sigma) (hi : Function.Injective i)
    (F : SmoothFunctions H sigma) (hF : ∀ x, ∃ u, i u = eval H sigma F x) :
    Function.support (eval H rho (injectiveLift H i hi F hF)) =
      Function.support (eval H sigma F) := by
  ext x
  simp only [Function.mem_support, ne_eq]
  rw [← injectiveLift_eval H i hi F hF x, map_eq_zero_iff i hi]

/-- The compactly supported version of `injectiveLift`. -/
def injectiveCompactLift (i : rho.IntertwiningMap sigma) (hi : Function.Injective i)
    (F : CompactFunctions H sigma) (hF : ∀ x, ∃ u, i u = eval H sigma F.1 x) :
    CompactFunctions H rho :=
  ⟨injectiveLift H i hi F.1 hF, by
    change IsCompact (quotientSupport H (eval H rho (injectiveLift H i hi F.1 hF)))
    rw [quotientSupport, support_injectiveLift]
    exact F.2⟩

end Exactness

/-- Exactness of smooth and compact induction (Renard III.2.2). -/
theorem inductionExactness [T2Space G]
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup)
    (hH : IsClosed (H : Set G)) :
    InductionExactnessClause (U := U) (V := V) (W := W) H := by
  intro rho sigma tau i p hi hp hexact hsigma
  have htau : IsSmooth tau := by
    intro w
    obtain ⟨v, rfl⟩ := hp w
    obtain ⟨K, hK⟩ := hsigma v
    refine ⟨K, ?_⟩
    intro k
    change tau (k : H) (p v) = p v
    rw [← Representation.IntertwiningMap.isIntertwining _ _ p]
    exact congrArg p (hK k)
  have hval : ∀ v, p v = 0 → ∃ u, i u = v := by
    intro v hv
    have hmem : v ∈ LinearMap.ker p.toLinearMap := hv
    rw [← hexact] at hmem
    exact hmem
  have hpi : ∀ u, p (i u) = 0 := by
    intro u
    have hmem : i u ∈ LinearMap.range i.toLinearMap := ⟨u, rfl⟩
    rw [hexact] at hmem
    exact hmem
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f f' hff
    apply structural_smooth_ext H
    intro x
    apply hi
    exact congrArg (fun F => eval H sigma F x) hff
  · apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      apply structural_smooth_ext H
      intro x
      exact hpi (eval H rho f x)
    · intro F hF
      have hF' : ∀ x, p (eval H sigma F x) = 0 := fun x =>
        congrArg (fun F' => eval H tau F' x) hF
      exact ⟨injectiveLift H i hi F (fun x => hval _ (hF' x)),
        structural_smooth_ext H fun x =>
          injectiveLift_eval H i hi F (fun y => hval _ (hF' y)) x⟩
  · exact smoothInductionSurjectivity G hcofinal H hH V W sigma tau hsigma htau p hp
  · intro f f' hff
    apply compactFunctions_ext H rho
    intro x
    apply hi
    exact congrArg (fun F => eval H sigma F.1 x) hff
  · apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      apply compactFunctions_ext H tau
      intro x
      exact hpi (eval H rho f.1 x)
    · intro F hF
      have hF' : ∀ x, p (eval H sigma F.1 x) = 0 := fun x =>
        congrArg (fun F' : CompactFunctions H tau => eval H tau F'.1 x) hF
      exact ⟨injectiveCompactLift H i hi F (fun x => hval _ (hF' x)),
        compactFunctions_ext H sigma fun x =>
          injectiveLift_eval H i hi F.1 (fun y => hval _ (hF' y)) x⟩
  · exact compactInductionSurjectivity G hcofinal H hH V W sigma tau hsigma htau p hp

/-! ### Central action -/

/-- A central character of the inducing representation passes to both induced
representations. -/
theorem inductionCentralAction : InductionCentralActionClause (V := V) H := by
  intro hZH chi sigma hsigma
  have key : ∀ (z : Subgroup.center G) (f : SmoothFunctions H sigma) (x : G),
      eval H sigma f (x * (z : G)) = (chi z : ℂ) • eval H sigma f x := by
    intro z f x
    rw [Subgroup.mem_center_iff.mp z.2 x, eval_covariant H sigma f ⟨(z : G), hZH z.2⟩ x,
      hsigma z]
  refine ⟨fun z f => structural_smooth_ext H fun x => key z f x,
    fun z f => compactFunctions_ext H sigma fun x => key z f.1 x⟩

/-! ### Induction in stages -/

/-- Smooth and compact induction in stages through a closed intermediate subgroup. -/
theorem inductionTransitivity [LocallyCompactSpace G] (hH : IsClosed (H : Set G)) :
    InductionTransitivityClause (V := V) H := by
  intro P hHP hP rho _hrho
  exact ⟨⟨smoothStagesEquiv H P hHP rho, fun _ _ => rfl⟩,
    ⟨compactStagesEquiv H P hHP rho hH hP, fun _ _ => rfl⟩⟩

/-! ### The open-subgroup adjunction -/

/-- Compact induction from an open subgroup is left adjoint to restriction, as an actual
linear equivalence of intertwiner spaces. -/
def openSubgroupAdjunctionEquiv (hH : IsOpen (H : Set G)) (sigma : Representation ℂ H V)
    (tau : Representation ℂ G W) (hsigma : IsSmooth sigma) :
    ((compactInduced H sigma).IntertwiningMap tau) ≃ₗ[ℂ]
      (Representation.IntertwiningMap sigma (tau.comp H.subtype)) where
  toFun T := (resIntertwining H tau T).comp (unitMap H hH sigma hsigma)
  invFun φ := cosetSum H hH tau sigma φ
  map_add' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  left_inv T := Representation.IntertwiningMap.ext (LinearMap.ext fun f => by
    change cosetSum H hH tau sigma ((resIntertwining H tau T).comp (unitMap H hH sigma hsigma))
      f = T f
    rw [cosetSum_resIntertwining_comp, cosetSum_unitMap])
  right_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    cosetSum_comp_unitMap H hH tau sigma hsigma φ v)

/-- The open-subgroup adjunction clause, with the support formula. -/
theorem openSubgroupAdjunction : OpenSubgroupAdjunctionClause (V := V) (W := W) H := by
  intro hH sigma tau hsigma _htau
  refine ⟨openSubgroupAdjunctionEquiv H hH sigma tau hsigma, ?_⟩
  intro T f hf
  change T (unitMap H hH sigma hsigma (eval H sigma f.1 1)) = T f
  congr 1
  apply compactFunctions_ext H sigma
  intro x
  rw [unitMap_apply, eval_unitFunction]
  by_cases hx : x ∈ H
  · simp only [hx, ↓reduceDIte]
    have hcov := eval_covariant H sigma f.1 ⟨x, hx⟩ 1
    rw [mul_one] at hcov
    exact hcov.symm
  · simp only [hx, ↓reduceDIte]
    exact (hf x hx).symm

end Clauses

/-- Structural properties of smooth and compact induction (Renard III.2.2–III.2.8). -/
theorem structuralStatement_holds :
    StructuralStatement (G := G) (U := U) (V := V) (W := W) := by
  intro _ _ hBasis H hH
  have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup := by
    intro K
    obtain ⟨L, hLc, hLK⟩ := hBasis (K : Set G) K.isOpen K.one_mem
    exact ⟨L, hLc, fun x hx => hLK hx⟩
  have : LocallyCompactSpace G := locallyCompactSpace_of_compactOpenBasis hBasis
  exact ⟨smoothFrobenius H, inductionExactness H hcofinal hH, compactQuotientClause_holds H,
    inductionTwist H, inductionCentralAction H, inductionTransitivity H hH,
    openSubgroupAdjunction H⟩

end Langlands.Induction
