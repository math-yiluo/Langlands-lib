import Langlands.Representation.Clifford.Twist
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.FiniteQuotientSemisimplicity
import Langlands.Representation.FiniteVectors
import Mathlib.RepresentationTheory.Maschke

/-! # Tensor factors over a normal subgroup

Let `N` be a normal subgroup of a group `G`, and let `κ` be a finite-dimensional complex
representation of `G`.

* If `κ` and a finite-dimensional representation `τ` of `G` have a nonzero intertwiner on `N`,
  then there is an irreducible representation `ξ` of `G`, trivial on `N`, with a nonzero
  intertwiner `κ ⊗ ξ → τ` (`exists_irreducible_tensor_intertwining`). The representation `ξ` is
  an irreducible subrepresentation of `Hom_N(κ, τ)`, on which `G` acts by
  `g · f = τ(g) ∘ f ∘ κ(g)⁻¹`, and the intertwiner is evaluation.
* If every operator `ρ(g)` is some `ρ(ι(x))`, then the pullback `ρ ∘ ι` is irreducible exactly
  when `ρ` is (`isIrreducible_comp_iff`).

The module also records the semisimplicity of a representation that factors through a finite
quotient (Maschke's theorem), the existence of an irreducible subrepresentation through a
character eigenvector of a semisimple finite-dimensional representation, and the transport of a
finite-dimensional representation to coordinates.
-/

noncomputable section

namespace Langlands.Clifford

open Representation Module
open scoped TensorProduct

universe uG uH uV uW uY

section Atoms

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero subrepresentation of a finite-dimensional representation contains an atom of the
lattice of subrepresentations, that is, an irreducible subrepresentation. -/
theorem exists_isAtom_le [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    {S : Subrepresentation ρ} (hS : S ≠ ⊥) : ∃ T : Subrepresentation ρ, T ≤ S ∧ IsAtom T := by
  have hmono : StrictMono
      (Subrepresentation.toSubmodule : Subrepresentation ρ → Submodule ℂ V) :=
    fun a b h => lt_of_le_of_ne (fun x hx => h.le hx)
      (fun e => h.ne (Subrepresentation.toSubmodule_injective e))
  have : WellFoundedLT (Subrepresentation ρ) := hmono.wellFoundedLT
  have : IsAtomic (Subrepresentation ρ) := inferInstance
  obtain h | ⟨T, hT, hTS⟩ := eq_bot_or_exists_atom_le S
  · exact absurd h hS
  · exact ⟨T, hTS, hT⟩

end Atoms

section Semisimple

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **Maschke's theorem through a finite quotient.** A complex representation that is trivial on
a normal subgroup of finite index is semisimple. -/
theorem isSemisimpleRepresentation_of_trivial_on_normal (ρ : Representation ℂ G V)
    (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (hN : ∀ n ∈ N, ρ n = 1) :
    ρ.IsSemisimpleRepresentation := by
  let ρ' : Representation ℂ (G ⧸ N) V :=
    QuotientGroup.lift N ρ (fun n hn => MonoidHom.mem_ker.mpr (hN n hn))
  have : NeZero (Nat.card (G ⧸ N) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hs : ρ'.IsSemisimpleRepresentation := inferInstance
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ' := ⟨U.toSubmodule, fun q v hv => by
    induction q using QuotientGroup.induction_on with
    | H g => exact U.apply_mem_toSubmodule g hv⟩
  obtain ⟨W, hW⟩ := exists_isCompl U'
  let W' : Subrepresentation ρ :=
    ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (g : G ⧸ N) hv⟩
  refine ⟨W', disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
  · exact Subrepresentation.toSubmodule_injective
      (congrArg (Subrepresentation.toSubmodule : Subrepresentation ρ' → Submodule ℂ V)
        hW.inf_eq_bot)
  · exact Subrepresentation.toSubmodule_injective
      (congrArg (Subrepresentation.toSubmodule : Subrepresentation ρ' → Submodule ℂ V)
        hW.sup_eq_top)

/-- **An irreducible subrepresentation through a character eigenvector.** Let `ρ` be a
semisimple finite-dimensional representation of `G`, let `ι : H → G` be a homomorphism and `θ` a
character of `H`. If `ρ` has a nonzero vector on which `H` acts by `θ`, then some irreducible
subrepresentation (an atom of the lattice of subrepresentations) has such a vector. -/
theorem exists_isAtom_eigen [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsSemisimpleRepresentation) {H : Type uH} [Group H] (ι : H →* G) (θ : H →* ℂˣ)
    {v : V} (hv : v ≠ 0) (hθ : ∀ h, ρ (ι h) v = (θ h : ℂ) • v) :
    ∃ Y : Subrepresentation ρ, IsAtom Y ∧
      ∃ w ∈ Y, w ≠ 0 ∧ ∀ h, ρ (ι h) w = (θ h : ℂ) • w := by
  classical
  have := hρ
  let E : Subrepresentation ρ → Prop := fun Z =>
    ∃ w ∈ Z, w ≠ 0 ∧ ∀ h, ρ (ι h) w = (θ h : ℂ) • w
  let P : ℕ → Prop := fun d => ∃ Y : Subrepresentation ρ, finrank ℂ Y.toSubmodule = d ∧ E Y
  have hP : ∃ d, P d := ⟨_, ⊤, rfl, v, Submodule.mem_top, hv, hθ⟩
  obtain ⟨Y, hYd, hYE⟩ := Nat.find_spec hP
  have hmin : ∀ Z : Subrepresentation ρ, E Z →
      finrank ℂ Y.toSubmodule ≤ finrank ℂ Z.toSubmodule :=
    fun Z hZ => hYd ▸ Nat.find_min' hP ⟨Z, rfl, hZ⟩
  have heq : ∀ {A B : Subrepresentation ρ}, A ≤ B →
      finrank ℂ B.toSubmodule ≤ finrank ℂ A.toSubmodule → A = B := fun {A B} hAB h =>
    Subrepresentation.toSubmodule_injective
      (Submodule.eq_of_le_of_finrank_le (fun x hx => hAB hx) h)
  obtain ⟨w, hwY, hw0, hwθ⟩ := hYE
  refine ⟨Y, ⟨?_, fun Z hZY => ?_⟩, w, hwY, hw0, hwθ⟩
  · intro hY
    rw [hY] at hwY
    exact hw0 ((Submodule.mem_bot ℂ).mp hwY)
  · obtain ⟨C, hC⟩ := exists_isCompl Z
    let p := FiniteQuotientAveraging.projectionOfIsCompl ρ Z C hC
    have hpθ : ∀ h, ρ (ι h) (p w) = (θ h : ℂ) • p w := fun h => by
      rw [← p.isIntertwining, hwθ, map_smul]
    by_cases hp : p w = 0
    · have hwC : w ∈ C := by
        have h1 : w ∈ LinearMap.ker (Z.toSubmodule.projection C.toSubmodule
            (FiniteQuotientAveraging.isCompl_toSubmodule ρ hC)) := hp
        rwa [Submodule.ker_projection] at h1
      have hYC : Y ⊓ C = Y := heq inf_le_left (hmin _ ⟨w, ⟨hwY, hwC⟩, hw0, hwθ⟩)
      have hZC : Z ≤ C := hZY.le.trans (inf_eq_left.mp hYC)
      exact eq_bot_iff.mpr (le_of_le_of_eq (le_inf le_rfl hZC) hC.inf_eq_bot)
    · exfalso
      have hpZ : p w ∈ Z := Submodule.projection_apply_mem _ w
      exact hZY.ne (heq hZY.le (hmin Z ⟨p w, hpZ, hp, hpθ⟩))

end Semisimple

section Orbits

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The orbit span of a vector fixed by a subgroup of finite index is finite-dimensional. -/
theorem finiteDimensional_orbitSpan_of_fixed (ρ : Representation ℂ G V) (K : Subgroup G)
    [K.FiniteIndex] {x : V} (hx : ∀ k ∈ K, ρ k x = x) :
    FiniteDimensional ℂ (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule := by
  let T := Submodule.span ℂ (Set.range fun q : G ⧸ K => ρ q.out x)
  have hT : (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    have hg : g = (QuotientGroup.mk g : G ⧸ K).out * (h : G)⁻¹ := by
      rw [hh, mul_inv_cancel_right]
    change ρ g x ∈ T
    rw [hg, map_mul, Module.End.mul_apply, hx _ (K.inv_mem h.2)]
    exact Submodule.subset_span ⟨_, rfl⟩
  have : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le hT

/-- A normal subgroup fixing a vector fixes its whole orbit span. -/
theorem apply_eq_of_mem_orbitSpan (ρ : Representation ℂ G V) (K : Subgroup G) [K.Normal]
    {x : V} (hx : ∀ k ∈ K, ρ k x = x) {y : V}
    (hy : y ∈ (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule) {k : G} (hk : k ∈ K) :
    ρ k y = y := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, rfl⟩ := hz
    have hc : g⁻¹ * k * g ∈ K := Subgroup.Normal.conj_mem' ‹K.Normal› k hk g
    rw [← Module.End.mul_apply, ← map_mul, show k * g = g * (g⁻¹ * k * g) by group, map_mul,
      Module.End.mul_apply, hx _ hc]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

end Orbits

section Coordinates

variable {G : Type uG} [Group G] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
  [FiniteDimensional ℂ Y]

/-- A finite-dimensional representation, transported to coordinates in `Module.finBasis`. -/
def coordinateRep (σ : Representation ℂ G Y) : Representation ℂ G (Fin (finrank ℂ Y) → ℂ) :=
  (MonoidHom.ofClass ((Module.finBasis ℂ Y).equivFun.conjAlgEquiv ℂ)).comp σ

/-- The coordinate isomorphism as an equivalence of representations. -/
def coordinateEquiv (σ : Representation ℂ G Y) : Representation.Equiv σ (coordinateRep σ) :=
  Representation.Equiv.mk (Module.finBasis ℂ Y).equivFun fun g => by
    apply LinearMap.ext
    intro x
    change _ = (Module.finBasis ℂ Y).equivFun
      (σ g ((Module.finBasis ℂ Y).equivFun.symm ((Module.finBasis ℂ Y).equivFun x)))
    rw [LinearEquiv.symm_apply_apply]
    rfl

theorem coordinateRep_eq_one {σ : Representation ℂ G Y} {g : G} (hg : σ g = 1) :
    coordinateRep σ g = 1 := by
  apply LinearMap.ext
  intro x
  change (Module.finBasis ℂ Y).equivFun (σ g ((Module.finBasis ℂ Y).equivFun.symm x)) = x
  rw [hg, Module.End.one_apply, LinearEquiv.apply_symm_apply]

end Coordinates

section TensorFactor

variable {G : Type uG} [Group G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Evaluation `κ ⊗ T → τ`, `w ⊗ f ↦ f w`, on a subrepresentation `T` of `Hom(κ, τ)`. -/
def evalIntertwining (κ : Representation ℂ G W) (τ : Representation ℂ G V)
    (T : Subrepresentation (linHom κ τ)) :
    (κ.tprod T.toRepresentation).IntertwiningMap τ where
  toLinearMap := TensorProduct.lift (T.toSubmodule.subtype).flip
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro w f
    change ((linHom κ τ g) (f : W →ₗ[ℂ] V)) (κ g w) = τ g ((f : W →ₗ[ℂ] V) w)
    rw [linHom_apply]
    change τ g ((f : W →ₗ[ℂ] V) (κ g⁻¹ (κ g w))) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem evalIntertwining_tmul (κ : Representation ℂ G W) (τ : Representation ℂ G V)
    (T : Subrepresentation (linHom κ τ)) (w : W) (f : T.toSubmodule) :
    evalIntertwining κ τ T (w ⊗ₜ f) = (f : W →ₗ[ℂ] V) w := rfl

/-- **Splitting off a tensor factor.** Let `ι : H → G` be a homomorphism with normal image and
let `κ`, `τ` be finite-dimensional representations of `G`. If their pullbacks to `H` have a
nonzero intertwiner, then there is an irreducible representation `ξ` of `G` on a coordinate space,
trivial on the image of `ι` and on every element acting trivially in both `κ` and `τ`, with a
nonzero intertwiner `κ ⊗ ξ → τ`. -/
theorem exists_irreducible_tensor_intertwining {H : Type uH} [Group H] (ι : H →* G)
    [ι.range.Normal] [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    (κ : Representation ℂ G W) (τ : Representation ℂ G V)
    (P : IntertwiningMap (κ.comp ι) (τ.comp ι)) (hP : P ≠ 0) :
    ∃ (d : ℕ) (ξ : Representation ℂ G (Fin d → ℂ)), ξ.IsIrreducible ∧ (∀ h, ξ (ι h) = 1) ∧
      (∀ g, κ g = 1 → τ g = 1 → ξ g = 1) ∧
      ∃ F : (κ.tprod ξ).IntertwiningMap τ, F ≠ 0 := by
  classical
  let S := restrictIntertwiners ι.range κ τ
  have hPmem : P.toLinearMap ∈ S.toSubmodule := by
    rintro ⟨_, h, rfl⟩
    change τ (ι h) ∘ₗ P.toLinearMap ∘ₗ κ (ι h)⁻¹ = P.toLinearMap
    apply LinearMap.ext
    intro w
    change τ (ι h) (P (κ (ι h)⁻¹ w)) = P w
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ P h (κ (ι h)⁻¹ w)
    change P (κ (ι h) (κ (ι h)⁻¹ w)) = τ (ι h) (P (κ (ι h)⁻¹ w)) at h1
    rw [← h1, ← Module.End.mul_apply, ← map_mul]
    simp
  have hS : S ≠ ⊥ := by
    intro h
    apply hP
    have hP0 : P.toLinearMap ∈ (⊥ : Subrepresentation (linHom κ τ)).toSubmodule := h ▸ hPmem
    ext w
    have hP0' : P.toLinearMap = 0 := (Submodule.mem_bot ℂ).mp hP0
    exact LinearMap.congr_fun hP0' w
  obtain ⟨T, hTS, hT⟩ := exists_isAtom_le (linHom κ τ) hS
  have hTirr := FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom T hT
  let e := coordinateEquiv T.toRepresentation
  refine ⟨_, coordinateRep T.toRepresentation, isIrreducible_of_equiv e hTirr, ?_, ?_, ?_⟩
  · intro h
    apply coordinateRep_eq_one
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact hTS f.2 ⟨ι h, h, rfl⟩
  · intro g hκg hτg
    apply coordinateRep_eq_one
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change linHom κ τ g (f : W →ₗ[ℂ] V) = f
    have hκinv : κ g⁻¹ = 1 := by
      calc κ g⁻¹ = κ g⁻¹ * κ g := by rw [hκg, mul_one]
        _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [linHom_apply, hτg, hκinv]
    rfl
  · refine ⟨(evalIntertwining κ τ T).comp
      (IntertwiningMap.lTensor κ e.symm.toIntertwiningMap), ?_⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨f, hfT, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (LinearMap.ext hcon)
    intro hF
    apply hw
    have h1 := congrArg (fun F : (κ.tprod (coordinateRep T.toRepresentation)).IntertwiningMap τ =>
      F (w ⊗ₜ e ⟨f, hfT⟩)) hF
    change evalIntertwining κ τ T (w ⊗ₜ e.symm (e ⟨f, hfT⟩)) = 0 at h1
    rw [Representation.Equiv.symm_apply_apply, evalIntertwining_tmul] at h1
    exact h1

end TensorFactor

section Pullback

variable {G : Type uG} [Group G] {H : Type uH} [Group H] {V : Type uV} [AddCommGroup V]
  [Module ℂ V]

/-- The subrepresentations of a pullback `ρ ∘ ι` along a homomorphism `ι` whose image acts
through all of the image of `ρ` are those of `ρ`. -/
def subrepresentationCompOrderIso (ρ : Representation ℂ G V) (ι : H →* G)
    (hι : ∀ g, ∃ x, ρ g = ρ (ι x)) : Subrepresentation (ρ.comp ι) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    obtain ⟨x, hx⟩ := hι g
    rw [hx]
    exact W.apply_mem_toSubmodule x hv⟩
  invFun Z := ⟨Z.toSubmodule, fun x _ hv => Z.apply_mem_toSubmodule (ι x) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- If every operator `ρ(g)` is some `ρ(ι(x))`, then `ρ ∘ ι` is irreducible exactly when `ρ`
is. -/
theorem isIrreducible_comp_iff (ρ : Representation ℂ G V) (ι : H →* G)
    (hι : ∀ g, ∃ x, ρ g = ρ (ι x)) :
    Representation.IsIrreducible (ρ.comp ι) ↔ ρ.IsIrreducible :=
  (subrepresentationCompOrderIso ρ ι hι).isSimpleOrder_iff

end Pullback

end Langlands.Clifford
