import Langlands.Shimura.PEL.HarrisCoefficientPrimeValuation
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientDiagram

/-! # Scaled transporters of CM levels and their maps of Harris lattices

A transporter `b : V ⟶ U` of small CM levels with translating element `a` maps Harris's
lattice `ℒ_U` into `ℓ^{-e} ℒ_V` through the representation of `ι a = (unop a)⁻¹`, for some
`e`. This file proves that such an exponent exists. It builds the category of levels with an
exponent, whose arrows are transporters together with an admissible exponent difference, and
the corresponding maps `x ↦ ℓ^e ρ(ι a) x` of lattices, which are strictly functorial.
See `HarrisTaylorCMScaledLevels.md`.
-/

noncomputable section

set_option autoImplicit false

universe u

open scoped TensorProduct
open Filter Topology

namespace Langlands.Shimura.Coefficients

open Langlands.Global AdelicFunctoriality AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ)

/-- At one place `l` above `p`: if `m` has valuation `< 1`, some power of `m` moves the
translate by any `g` of the compact-level lattice of `U` into that of `V`. -/
theorem exists_pow_smul_placeAction_mem (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
    (m : ℕ) (hm : Valued.v ((m : ℕ) : FiniteCompletion L l) < 1)
    (g : σ.FiniteAdelicPoints) (U V : CompactOpenLevel σ.FiniteAdelicPoints) :
    ∃ e : ℕ, ∀ x ∈ (algebraicCompactCoefficientLattice ρ p l U).carrier,
      (m ^ e) • ρ.placeAction p l g x ∈ (algebraicCompactCoefficientLattice ρ p l V).carrier := by
  let _ := coefficientTopology L l W
  set Λ := (algebraicCompactCoefficientLattice ρ p l U).carrier
  set Λ' := (algebraicCompactCoefficientLattice ρ p l V).carrier
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := FiniteCompletion L l)
  obtain ⟨s, hs⟩ := hfg
  have hopen := algebraicCompactCoefficientLattice_isOpen ρ p l V
  have hpow : Tendsto (fun e : ℕ => ((m : FiniteCompletion L l)) ^ e) atTop (𝓝 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hm
  have hev : ∀ y : FiniteCompletion L l ⊗[L] W,
      ∀ᶠ e : ℕ in atTop, ((m : FiniteCompletion L l) ^ e) • y ∈ Λ' := by
    intro y
    have ht : Tendsto (fun e : ℕ => ((m : FiniteCompletion L l) ^ e) • y) atTop (𝓝 0) := by
      simpa using hpow.smul_const y
    exact ht (hopen.mem_nhds Λ'.zero_mem)
  have hall : ∀ᶠ e : ℕ in atTop, ∀ y ∈ s,
      ((m : FiniteCompletion L l) ^ e) • ρ.placeAction p l g y ∈ Λ' :=
    (Filter.eventually_all_finset s).2 (fun y _ => hev _)
  obtain ⟨e, he⟩ := hall.exists
  have key : ∀ z : FiniteCompletion L l ⊗[L] W,
      (m ^ e) • z = ((m : FiniteCompletion L l) ^ e) • z := by
    intro z
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine ⟨e, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => rw [key]; exact he y hy
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact Λ'.add_mem hy hz
  | smul a y _ hy =>
    rw [LinearMapClass.map_smul_of_tower, smul_comm]
    exact Λ'.smul_mem a hy

/-- If `m` has valuation `< 1` at every place above `p`, some power of `m` moves the translate
by any `g` of Harris's lattice of `U` into Harris's lattice of `V`. -/
theorem exists_pow_smul_harrisAdelic_mem (m : ℕ)
    (hm : ∀ l : FinitePlacesAbove L p, Valued.v ((m : ℕ) : FiniteCompletion L l.1) < 1)
    (g : σ.FiniteAdelicPoints) (U V : CompactOpenLevel σ.FiniteAdelicPoints) :
    ∃ e : ℕ, ∀ x ∈ harrisLattice ρ p U, (m ^ e) • ρ.harrisAdelic p g x ∈ harrisLattice ρ p V := by
  choose e he using fun l : FinitePlacesAbove L p =>
    exists_pow_smul_placeAction_mem ρ p l.1 m (hm l) g U V
  obtain ⟨N, hN⟩ := (Set.finite_range e).bddAbove
  refine ⟨N, fun x hx => ?_⟩
  rw [mem_harrisLattice] at hx ⊢
  intro l
  have hle : e l ≤ N := hN ⟨l, rfl⟩
  rw [map_nsmul, ρ.harrisCoefficientEquiv_adelic, Pi.smul_apply, ρ.harrisProductAdelic_apply,
    ← Nat.sub_add_cancel hle, pow_add, mul_smul]
  exact (algebraicCompactCoefficientLattice ρ p l.1 V).carrier.smul_of_tower_mem _
    (he l _ (hx l))

end Langlands.Shimura.Coefficients

open CategoryTheory Opposite

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.Global Langlands.Shimura.Coefficients

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {d : ℕ} (D : CentralSimpleUnitaryData E F A d)

/-! ## The ordinary element of a transporter -/

/-- The element `ι a = (unop a)⁻¹` of the finite-adelic group attached to a transporter
`b : V ⟶ U` of small CM levels with translating element `a` of the opposite group. -/
def smallCMArrowElement {V U : SmallCMLevel D} (b : V ⟶ U) :
    D.rationalInvolution.FiniteAdelicPoints :=
  (MulOpposite.unop b.hom.element)⁻¹

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMArrowElement_id (U : SmallCMLevel D) :
    smallCMArrowElement D (𝟙 U) = 1 := by
  simp [smallCMArrowElement]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The ordinary element of a composite is the product in the order of composition. -/
theorem smallCMArrowElement_comp {W V U : SmallCMLevel D} (b' : W ⟶ V) (b : V ⟶ U) :
    smallCMArrowElement D (b' ≫ b) = smallCMArrowElement D b' * smallCMArrowElement D b := by
  simp [smallCMArrowElement, mul_inv_rev]

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ)

/-! ## Admissible exponents -/

/-- The exponent `e` is admissible for the transporter `b : V ⟶ U`: the map
`x ↦ ℓ^e ρ(ι b) x` sends Harris's lattice of `U` into that of `V`, where `ℓ` is the coefficient
prime of `p`. -/
def CMHarrisLatticeScaled {V U : SmallCMLevel D} (b : V ⟶ U) (e : ℕ) : Prop :=
  ∀ x ∈ harrisLattice ρ p (CompactOpenLevel.inverseOpposite U.obj),
    (harrisCoefficientPrime p ^ e) • ρ.harrisAdelic p (smallCMArrowElement D b) x ∈
      harrisLattice ρ p (CompactOpenLevel.inverseOpposite V.obj)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Every transporter has an admissible exponent. -/
theorem exists_cmHarrisLatticeScaled {V U : SmallCMLevel D} (b : V ⟶ U) :
    ∃ e : ℕ, CMHarrisLatticeScaled D ρ p b e :=
  exists_pow_smul_harrisAdelic_mem ρ p _ (fun l => harrisCoefficientPrime_valued_lt_one p l) _ _ _

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Larger exponents remain admissible. -/
theorem CMHarrisLatticeScaled.mono {V U : SmallCMLevel D} {b : V ⟶ U} {e e' : ℕ}
    (h : CMHarrisLatticeScaled D ρ p b e) (he : e ≤ e') : CMHarrisLatticeScaled D ρ p b e' := by
  intro x hx
  rw [← Nat.sub_add_cancel he, pow_add, mul_smul]
  exact nsmul_mem (h x hx) _

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The exponent `0` is admissible for an identity. -/
theorem cmHarrisLatticeScaled_id (U : SmallCMLevel D) :
    CMHarrisLatticeScaled D ρ p (𝟙 U) 0 := by
  intro x hx
  simpa using hx

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Admissible exponents add along composites. -/
theorem CMHarrisLatticeScaled.comp {W V U : SmallCMLevel D} {b' : W ⟶ V} {b : V ⟶ U}
    {e' e : ℕ} (h' : CMHarrisLatticeScaled D ρ p b' e') (h : CMHarrisLatticeScaled D ρ p b e) :
    CMHarrisLatticeScaled D ρ p (b' ≫ b) (e + e') := by
  intro x hx
  have := h' _ (h x hx)
  rw [map_nsmul, smul_smul, ← pow_add, add_comm] at this
  rw [smallCMArrowElement_comp, map_mul, LinearEquiv.mul_apply]
  exact this

/-! ## The category of scaled levels -/

/-- A small CM level together with an exponent. The representation `ρ` and the place `p`
determine the morphisms. -/
@[nolint unusedArguments]
structure CMScaledLevel (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
    (p : Global.FinitePlace ℚ) where
  /-- The level. -/
  level : SmallCMLevel D
  /-- The exponent. -/
  scale : ℕ

/-- A morphism of scaled levels: a transporter of levels whose exponent difference is
admissible. -/
@[ext] structure CMScaledLevel.Hom (X Y : CMScaledLevel D ρ p) where
  /-- The transporter of levels. -/
  hom : X.level ⟶ Y.level
  le : X.scale ≤ Y.scale
  scaled : CMHarrisLatticeScaled D ρ p hom (Y.scale - X.scale)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Scaled levels and admissible transporters form a category. -/
instance : Category (CMScaledLevel D ρ p) where
  Hom := CMScaledLevel.Hom D ρ p
  id X := ⟨𝟙 X.level, le_rfl, by simpa using cmHarrisLatticeScaled_id D ρ p X.level⟩
  comp f g := ⟨f.hom ≫ g.hom, f.le.trans g.le, by
    have h := CMHarrisLatticeScaled.comp D ρ p f.scaled g.scaled
    have e : _ - _ + (_ - _) = _ - _ := Nat.sub_add_sub_cancel g.le f.le
    rwa [e] at h⟩
  id_comp f := by ext; exact Category.id_comp _
  comp_id f := by ext; exact Category.comp_id _
  assoc f g h := by ext; exact Category.assoc _ _ _

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem CMScaledLevel.id_hom (X : CMScaledLevel D ρ p) :
    CMScaledLevel.Hom.hom (𝟙 X) = 𝟙 X.level := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem CMScaledLevel.comp_hom {X Y Z : CMScaledLevel D ρ p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CMScaledLevel.Hom.hom (f ≫ g) = CMScaledLevel.Hom.hom f ≫ CMScaledLevel.Hom.hom g := rfl

/-- The same transporter with both exponents raised by `k`. -/
def CMScaledLevel.Hom.shift {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k : ℕ) :
    (⟨X.level, k + X.scale⟩ : CMScaledLevel D ρ p) ⟶ ⟨Y.level, k + Y.scale⟩ :=
  ⟨CMScaledLevel.Hom.hom (X := X) (Y := Y) f,
    Nat.add_le_add_left (CMScaledLevel.Hom.le (X := X) (Y := Y) f) k, by
    have e : k + Y.scale - (k + X.scale) = Y.scale - X.scale := Nat.add_sub_add_left _ _ _
    rw [e]
    exact CMScaledLevel.Hom.scaled (X := X) (Y := Y) f⟩

/-- The identity transporter from a level with a smaller exponent to the same level with a larger
one. -/
def CMScaledLevel.raise (U : SmallCMLevel D) {n n' : ℕ} (h : n ≤ n') :
    (⟨U, n⟩ : CMScaledLevel D ρ p) ⟶ ⟨U, n'⟩ :=
  ⟨𝟙 U, h, (cmHarrisLatticeScaled_id D ρ p U).mono D ρ p (Nat.zero_le _)⟩

/-! ## Maps of lattices -/

/-- The map of Harris lattices of a morphism `f : X ⟶ Y` of scaled levels: `x ↦ ℓ^e ρ(ι b) x`
from the lattice of the level of `Y` to that of the level of `X`, where `b` is the transporter
of `f` and `e` is the exponent difference. -/
def cmHarrisLatticeTransport {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) :
    harrisLattice ρ p (CompactOpenLevel.inverseOpposite Y.level.obj) →ₗ[
      HarrisCoefficientIntegers K p]
      harrisLattice ρ p (CompactOpenLevel.inverseOpposite X.level.obj) :=
  ((harrisCoefficientPrime p ^ (Y.scale - X.scale)) •
    LinearMap.restrictScalars (HarrisCoefficientIntegers K p)
      (ρ.harrisAdelic p (smallCMArrowElement D (CMScaledLevel.Hom.hom f))).toLinearMap).restrict
    (CMScaledLevel.Hom.scaled f)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The underlying vector of the lattice map. -/
theorem cmHarrisLatticeTransport_coe {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y)
    (x : harrisLattice ρ p (CompactOpenLevel.inverseOpposite Y.level.obj)) :
    (cmHarrisLatticeTransport D ρ p f x : (K ⊗[ℚ] FiniteCompletion ℚ p) ⊗[K] W) =
      (harrisCoefficientPrime p ^ (Y.scale - X.scale)) •
        ρ.harrisAdelic p (smallCMArrowElement D (CMScaledLevel.Hom.hom f)) x := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The lattice map of an identity is the identity. -/
@[simp] theorem cmHarrisLatticeTransport_id (X : CMScaledLevel D ρ p) :
    cmHarrisLatticeTransport D ρ p (𝟙 X) = LinearMap.id := by
  ext x
  simp [cmHarrisLatticeTransport_coe]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The lattice maps are contravariantly functorial. -/
theorem cmHarrisLatticeTransport_comp {X Y Z : CMScaledLevel D ρ p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cmHarrisLatticeTransport D ρ p (f ≫ g) =
      (cmHarrisLatticeTransport D ρ p f).comp (cmHarrisLatticeTransport D ρ p g) := by
  ext x
  simp only [LinearMap.comp_apply, cmHarrisLatticeTransport_coe, CMScaledLevel.comp_hom,
    smallCMArrowElement_comp, map_mul, LinearEquiv.mul_apply, map_nsmul, smul_smul, ← pow_add]
  congr 2
  have h1 := CMScaledLevel.Hom.le f
  have h2 := CMScaledLevel.Hom.le g
  omega

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Raising the exponent multiplies the lattice map by the corresponding power of `ℓ`. -/
theorem cmHarrisLatticeTransport_raise (U : SmallCMLevel D) {n n' : ℕ} (h : n ≤ n')
    (x : harrisLattice ρ p (CompactOpenLevel.inverseOpposite U.obj)) :
    (cmHarrisLatticeTransport D ρ p (CMScaledLevel.raise D ρ p U h) x :
        (K ⊗[ℚ] FiniteCompletion ℚ p) ⊗[K] W) =
      (harrisCoefficientPrime p ^ (n' - n)) • (x : (K ⊗[ℚ] FiniteCompletion ℚ p) ⊗[K] W) := by
  rw [cmHarrisLatticeTransport_coe]
  simp [CMScaledLevel.raise]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Shifting both exponents does not change the lattice map. -/
theorem cmHarrisLatticeTransport_shift {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k : ℕ) :
    cmHarrisLatticeTransport D ρ p (CMScaledLevel.Hom.shift D ρ p f k) =
      cmHarrisLatticeTransport D ρ p f := by
  ext x
  simp only [cmHarrisLatticeTransport_coe]
  rw [show k + Y.scale - (k + X.scale) = Y.scale - X.scale from Nat.add_sub_add_left _ _ _]
  rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Equivariance: the lattice map intertwines the action of `(ι b)⁻¹ g (ι b)` on the target
level's lattice with the action of `g` on the source level's lattice. -/
theorem cmHarrisLatticeTransport_harrisAdelic {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y)
    (g : D.rationalInvolution.FiniteAdelicPoints)
    (x y : harrisLattice ρ p (CompactOpenLevel.inverseOpposite Y.level.obj))
    (hy : (y : (K ⊗[ℚ] FiniteCompletion ℚ p) ⊗[K] W) =
      ρ.harrisAdelic p ((smallCMArrowElement D (CMScaledLevel.Hom.hom f))⁻¹ * g *
        smallCMArrowElement D (CMScaledLevel.Hom.hom f)) x) :
    (cmHarrisLatticeTransport D ρ p f y : (K ⊗[ℚ] FiniteCompletion ℚ p) ⊗[K] W) =
      ρ.harrisAdelic p g (cmHarrisLatticeTransport D ρ p f x) := by
  rw [cmHarrisLatticeTransport_coe, cmHarrisLatticeTransport_coe, hy, map_nsmul,
    ← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul, ← mul_assoc,
    ← mul_assoc, mul_inv_cancel, one_mul]

/-! ## Maps of torsion coefficient modules -/

local notation "Iℓ" => harrisCoefficientScalarIdeal K p (harrisCoefficientPrime p)

/-- The map of `ℓ`-power torsion coefficient modules of a morphism `f : X ⟶ Y` of scaled levels,
from stage `k` of the level of `Y` to stage `k' ≤ k` of the level of `X`: reduce the lattice
map modulo `ℓ^k`, then reduce from `ℓ^k` to `ℓ^{k'}`. -/
def cmHarrisTorsionTransport {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) {k' k : ℕ} (h : k' ≤ k) :
    ((cmHarrisTorsionSystem D ρ p Y.level (harrisCoefficientPrime p)).obj (op k)).V ⟶
      ((cmHarrisTorsionSystem D ρ p X.level (harrisCoefficientPrime p)).obj (op k')).V :=
  (Langlands.Coefficients.AdicSystem.powerReduction Iℓ k).map
      (ModuleCat.ofHom (cmHarrisLatticeTransport D ρ p f)) ≫
    (Langlands.Coefficients.AdicSystem.transition Iℓ h).app _

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- On residues of lattice vectors, the torsion map is the residue of the lattice map. -/
@[simp] theorem cmHarrisTorsionTransport_mk {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y)
    {k' k : ℕ} (h : k' ≤ k)
    (x : (harrisLatticeAction ρ p (CompactOpenLevel.inverseOpposite Y.level.obj)).V) :
    (cmHarrisTorsionTransport D ρ p f h).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cmHarrisLatticeTransport D ρ p f x) := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The torsion maps are contravariantly functorial, composing the stage reductions. -/
theorem cmHarrisTorsionTransport_comp {X Y Z : CMScaledLevel D ρ p} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k'' k' k : ℕ} (h' : k'' ≤ k') (h : k' ≤ k) :
    cmHarrisTorsionTransport D ρ p (f ≫ g) (h'.trans h) =
      cmHarrisTorsionTransport D ρ p g h ≫ cmHarrisTorsionTransport D ρ p f h' := by
  ext x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (cmHarrisTorsionTransport D ρ p (f ≫ g) (h'.trans h)).hom (Submodule.Quotient.mk a) =
    (cmHarrisTorsionTransport D ρ p f h').hom
      ((cmHarrisTorsionTransport D ρ p g h).hom (Submodule.Quotient.mk a))
  rw [cmHarrisTorsionTransport_mk, cmHarrisTorsionTransport_mk]
  exact (congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (cmHarrisLatticeTransport_comp D ρ p f g) a)).trans
      (cmHarrisTorsionTransport_mk D ρ p f h' (cmHarrisLatticeTransport D ρ p g a)).symm

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- For an identity the torsion map is the stage reduction of the torsion system. -/
theorem cmHarrisTorsionTransport_id (X : CMScaledLevel D ρ p) {k' k : ℕ} (h : k' ≤ k) :
    cmHarrisTorsionTransport D ρ p (𝟙 X) h =
      ((cmHarrisTorsionSystem D ρ p X.level (harrisCoefficientPrime p)).map
        (homOfLE h).op).hom := by
  ext x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [cmHarrisTorsionTransport_mk, cmHarrisLatticeTransport_id]
  rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- For a raise of the exponent, the torsion map is the stage reduction multiplied by the
corresponding power of `ℓ`. -/
theorem cmHarrisTorsionTransport_raise (U : SmallCMLevel D) {n n' : ℕ} (hn : n ≤ n')
    {k' k : ℕ} (h : k' ≤ k) :
    cmHarrisTorsionTransport D ρ p (CMScaledLevel.raise D ρ p U hn) h =
      (harrisCoefficientPrime p ^ (n' - n)) •
        ((cmHarrisTorsionSystem D ρ p U (harrisCoefficientPrime p)).map (homOfLE h).op).hom := by
  ext x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e : cmHarrisLatticeTransport D ρ p (CMScaledLevel.raise D ρ p U hn) a =
      (harrisCoefficientPrime p ^ (n' - n)) • a :=
    Subtype.ext (cmHarrisLatticeTransport_raise D ρ p U hn a)
  change (cmHarrisTorsionTransport D ρ p (CMScaledLevel.raise D ρ p U hn) h).hom
      (Submodule.Quotient.mk a) =
    (harrisCoefficientPrime p ^ (n' - n)) •
      ((cmHarrisTorsionSystem D ρ p U (harrisCoefficientPrime p)).map
        (homOfLE h).op).hom.hom (Submodule.Quotient.mk a)
  rw [cmHarrisTorsionTransport_mk, e]
  rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Equivariance of the torsion maps: if `u = a⁻¹ v a` for the translating element `a` of the
transporter, the action of `u` at the level of `Y` corresponds to the action of `v` at the level
of `X`. -/
theorem cmHarrisTorsionTransport_comm {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) {k' k : ℕ}
    (h : k' ≤ k) (v : X.level.obj.subgroup) (u : Y.level.obj.subgroup)
    (hu : (u : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) =
      ((CMScaledLevel.Hom.hom f).hom.element)⁻¹ * v * (CMScaledLevel.Hom.hom f).hom.element) :
    ((cmHarrisTorsionSystem D ρ p Y.level (harrisCoefficientPrime p)).obj (op k)).ρ u ≫
        cmHarrisTorsionTransport D ρ p f h =
      cmHarrisTorsionTransport D ρ p f h ≫
        ((cmHarrisTorsionSystem D ρ p X.level (harrisCoefficientPrime p)).obj (op k')).ρ v := by
  ext x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hel : (CompactOpenLevel.inverseOppositeEquiv Y.level.obj u :
      D.rationalInvolution.FiniteAdelicPoints) =
      (smallCMArrowElement D (CMScaledLevel.Hom.hom f))⁻¹ *
        (CompactOpenLevel.inverseOppositeEquiv X.level.obj v :
          D.rationalInvolution.FiniteAdelicPoints) *
        smallCMArrowElement D (CMScaledLevel.Hom.hom f) := by
    simp only [CompactOpenLevel.inverseOppositeEquiv_coe, smallCMArrowElement, hu,
      MulOpposite.unop_mul, MulOpposite.unop_inv, mul_inv_rev, inv_inv, mul_assoc]
  have key := cmHarrisLatticeTransport_harrisAdelic D ρ p f
    (CompactOpenLevel.inverseOppositeEquiv X.level.obj v) a
    (((harrisLatticeAction ρ p (CompactOpenLevel.inverseOpposite Y.level.obj)).ρ
      (CompactOpenLevel.inverseOppositeEquiv Y.level.obj u)).hom a)
    ((harrisLatticeAction_apply ρ p _ (CompactOpenLevel.inverseOppositeEquiv Y.level.obj u)
      a).trans (by rw [hel]))
  exact congrArg Submodule.Quotient.mk (Subtype.ext key)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
