import Langlands.GroupScheme.LinearAdditiveExtension.EquivariantFunction
import Langlands.GroupScheme.HomDescent

/-! # A crossed homomorphism extending a closed additive subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearAdditiveExtension

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1
local notation "𝔻" => Diagonalizable.groupScheme (CommRingCat.of k) Λ

variable {E : GroupScheme (Spec (CommRingCat.of k))}
  (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-! ### Descent along the quotient map -/

section Descent

private abbrev fpqc : MorphismProperty Scheme.{u} := @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
theorem fpqc_whiskerRight [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] (Y : Over (Spec (CommRingCat.of k))) :
    fpqc (q.hom.hom ▷ Y).left := by
  rw [← tensorHom_id]
  exact MorphismProperty.pullbackMap (P := fpqc)
    ⟨inferInstance, inferInstance, inferInstance⟩
    ⟨inferInstance, inferInstance, inferInstance⟩
    (Over.w q.hom.hom).symm (Over.w (𝟙 Y)).symm

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

instance quasiCompact_whiskerRight (Y : Over (Spec (CommRingCat.of k))) :
    QuasiCompact (q.hom.hom ▷ Y).left := (fpqc_whiskerRight q Y).1

instance flat_whiskerRight (Y : Over (Spec (CommRingCat.of k))) :
    Flat (q.hom.hom ▷ Y).left := (fpqc_whiskerRight q Y).2.1

instance surjective_whiskerRight (Y : Over (Spec (CommRingCat.of k))) :
    Surjective (q.hom.hom ▷ Y).left := (fpqc_whiskerRight q Y).2.2

instance epi_whiskerRight (Y : Over (Spec (CommRingCat.of k))) : Epi (q.hom.hom ▷ Y) :=
  Over.epi_of_epi_left _

instance epi_q : Epi q.hom.hom := Over.epi_of_epi_left _

variable {W : Over (Spec (CommRingCat.of k))}

omit [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left] in
/-- Two points of `E` with the same image differ by a kernel point. -/
theorem eq_mul_kpt {T : Over (Spec (CommRingCat.of k))} {g g' : T ⟶ E.X}
    (h : g ≫ q.hom.hom = g' ≫ q.hom.hom) :
    g' = g * (kpt q g g' h ≫ (kernelι q).hom.hom) := by
  rw [kpt_comp, mul_inv_cancel_left]

omit [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left] in
theorem descend_rel (Ψ : E.X ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ Ψ = g ≫ Ψ)
    {Z : Scheme.{u}} (h₁ h₂ : Z ⟶ E.X.left) (he : h₁ ≫ q.hom.hom.left = h₂ ≫ q.hom.hom.left) :
    h₁ ≫ Ψ.left = h₂ ≫ Ψ.left := by
  have hs : h₂ ≫ E.X.hom = h₁ ≫ E.X.hom := by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← he, Category.assoc]
  let p₁ : Over.mk (h₁ ≫ E.X.hom) ⟶ E.X := Over.homMk h₁ rfl
  let p₂ : Over.mk (h₁ ≫ E.X.hom) ⟶ E.X := Over.homMk h₂ hs
  have hp : p₁ ≫ q.hom.hom = p₂ ≫ q.hom.hom := Over.OverMorphism.ext (by exact he)
  have := congrArg (fun x => x.left) (hΨ _ p₁ (kpt q p₁ p₂ hp))
  rw [← eq_mul_kpt q hp] at this
  exact this.symm

/-- The underlying scheme morphism of the descent through `q`. -/
def descendScheme (Ψ : E.X ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ Ψ = g ≫ Ψ) : (𝔻).X.left ⟶ W.left :=
  EffectiveEpi.desc q.hom.hom.left Ψ.left (fun h₁ h₂ he => descend_rel q Ψ hΨ h₁ h₂ he)

@[reassoc]
theorem fac_descendScheme (Ψ : E.X ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ Ψ = g ≫ Ψ) :
    q.hom.hom.left ≫ descendScheme q Ψ hΨ = Ψ.left :=
  EffectiveEpi.fac _ _ _

/-- Descend a morphism out of `E` that is invariant under right translation by the kernel. -/
def descend (Ψ : E.X ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ Ψ = g ≫ Ψ) : (𝔻).X ⟶ W :=
  Over.homMk (descendScheme q Ψ hΨ) (by
    apply (cancel_epi q.hom.hom.left).mp
    rw [fac_descendScheme_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_descend (Ψ : E.X ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ Ψ = g ≫ Ψ) :
    q.hom.hom ≫ descend q Ψ hΨ = Ψ :=
  Over.OverMorphism.ext (fac_descendScheme q Ψ hΨ)

variable {Y : Over (Spec (CommRingCat.of k))}

omit [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left] in
theorem descendLeft_rel (Ψ : E.X ⊗ Y ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (y : T ⟶ Y)
      (u : T ⟶ (kernel q).X),
      lift (g * (u ≫ (kernelι q).hom.hom)) y ≫ Ψ = lift g y ≫ Ψ)
    {Z : Scheme.{u}} (h₁ h₂ : Z ⟶ (E.X ⊗ Y).left)
    (he : h₁ ≫ (q.hom.hom ▷ Y).left = h₂ ≫ (q.hom.hom ▷ Y).left) :
    h₁ ≫ Ψ.left = h₂ ≫ Ψ.left := by
  have hs : h₂ ≫ (E.X ⊗ Y).hom = h₁ ≫ (E.X ⊗ Y).hom := by
    rw [← Over.w (q.hom.hom ▷ Y), ← Category.assoc, ← he, Category.assoc]
  let p₁ : Over.mk (h₁ ≫ (E.X ⊗ Y).hom) ⟶ E.X ⊗ Y := Over.homMk h₁ rfl
  let p₂ : Over.mk (h₁ ≫ (E.X ⊗ Y).hom) ⟶ E.X ⊗ Y := Over.homMk h₂ hs
  have hp : p₁ ≫ (q.hom.hom ▷ Y) = p₂ ≫ (q.hom.hom ▷ Y) := Over.OverMorphism.ext (by exact he)
  have hq : (p₁ ≫ fst E.X Y) ≫ q.hom.hom = (p₂ ≫ fst E.X Y) ≫ q.hom.hom := by
    have := congrArg (· ≫ fst (𝔻).X Y) hp
    simpa only [Category.assoc, whiskerRight_fst] using this
  have hy : p₁ ≫ snd E.X Y = p₂ ≫ snd E.X Y := by
    have := congrArg (· ≫ snd (𝔻).X Y) hp
    simpa only [Category.assoc, whiskerRight_snd] using this
  have h1 : p₁ = lift (p₁ ≫ fst E.X Y) (p₁ ≫ snd E.X Y) := by simp
  have h2 : p₂ = lift ((p₁ ≫ fst E.X Y) *
      (kpt q _ _ hq ≫ (kernelι q).hom.hom)) (p₁ ≫ snd E.X Y) := by
    rw [← eq_mul_kpt q hq, hy]
    simp
  have := hΨ _ (p₁ ≫ fst E.X Y) (p₁ ≫ snd E.X Y) (kpt q _ _ hq)
  rw [← h2, ← h1] at this
  exact (congrArg (fun x => x.left) this).symm

/-- The underlying scheme morphism of the descent through `q ▷ Y`. -/
def descendLeftScheme (Ψ : E.X ⊗ Y ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (y : T ⟶ Y)
      (u : T ⟶ (kernel q).X),
      lift (g * (u ≫ (kernelι q).hom.hom)) y ≫ Ψ = lift g y ≫ Ψ) :
    ((𝔻).X ⊗ Y).left ⟶ W.left :=
  EffectiveEpi.desc (q.hom.hom ▷ Y).left Ψ.left
    (fun h₁ h₂ he => descendLeft_rel q Ψ hΨ h₁ h₂ he)

@[reassoc]
theorem fac_descendLeftScheme (Ψ : E.X ⊗ Y ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (y : T ⟶ Y)
      (u : T ⟶ (kernel q).X),
      lift (g * (u ≫ (kernelι q).hom.hom)) y ≫ Ψ = lift g y ≫ Ψ) :
    (q.hom.hom ▷ Y).left ≫ descendLeftScheme q Ψ hΨ = Ψ.left :=
  EffectiveEpi.fac _ _ _

/-- Descend a morphism out of `E ⊗ Y` that is invariant under right translation of the first
factor by the kernel, along `q ▷ Y`. -/
def descendLeft (Ψ : E.X ⊗ Y ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (y : T ⟶ Y)
      (u : T ⟶ (kernel q).X),
      lift (g * (u ≫ (kernelι q).hom.hom)) y ≫ Ψ = lift g y ≫ Ψ) : (𝔻).X ⊗ Y ⟶ W :=
  Over.homMk (descendLeftScheme q Ψ hΨ) (by
    apply (cancel_epi (q.hom.hom ▷ Y).left).mp
    rw [fac_descendLeftScheme_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_descendLeft (Ψ : E.X ⊗ Y ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (y : T ⟶ Y)
      (u : T ⟶ (kernel q).X),
      lift (g * (u ≫ (kernelι q).hom.hom)) y ≫ Ψ = lift g y ≫ Ψ) :
    (q.hom.hom ▷ Y) ≫ descendLeft q Ψ hΨ = Ψ :=
  Over.OverMorphism.ext (fac_descendLeftScheme q Ψ hΨ)

theorem lift_comp_descendLeft (Ψ : E.X ⊗ Y ⟶ W)
    (hΨ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (y : T ⟶ Y)
      (u : T ⟶ (kernel q).X),
      lift (g * (u ≫ (kernelι q).hom.hom)) y ≫ Ψ = lift g y ≫ Ψ)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X) (y : T ⟶ Y) :
    lift (g ≫ q.hom.hom) y ≫ descendLeft q Ψ hΨ = lift g y ≫ Ψ := by
  rw [← lift_whiskerRight, Category.assoc, fac_descendLeft]

end Descent

/-! ### Points of products -/

theorem hom_ext_lift {X Y W : Over (Spec (CommRingCat.of k))} {α β : X ⊗ Y ⟶ W}
    (h : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (y : T ⟶ Y),
      lift x y ≫ α = lift x y ≫ β) : α = β := by
  simpa using h _ (fst X Y) (snd X Y)

theorem hom_ext_lift₃ {X Y Z W : Over (Spec (CommRingCat.of k))} {α β : X ⊗ (Y ⊗ Z) ⟶ W}
    (h : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      lift x (lift y z) ≫ α = lift x (lift y z) ≫ β) : α = β := by
  apply hom_ext_lift
  intro T x w
  have hw : w = lift (w ≫ fst Y Z) (w ≫ snd Y Z) := by simp
  rw [hw]
  exact h T x _ _

/-! ### The crossed homomorphism -/

section CrossedHom

variable (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
  (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
  (fE : E.X ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X)

/-- `Φ(g, x) = χ(g)⁻¹ (f(g x) − f(g))`. -/
def phi : E.X ⊗ E.X ⟶ (𝔾ₐ).X :=
  (VectorGroup.weightAction (n := 1) χ).act ((fst E.X E.X ≫ q.hom.hom)⁻¹)
    (((fst E.X E.X * snd E.X E.X) ≫ fE) * (fst E.X E.X ≫ fE)⁻¹)

theorem cd_lift_phi {T : Over (Spec (CommRingCat.of k))} (g x : T ⟶ E.X) :
    cd (lift g x ≫ phi q χ fE) =
      VectorGroup.charValue χ T (g ≫ q.hom.hom)⁻¹ * (cd ((g * x) ≫ fE) - cd (g ≫ fE)) := by
  rw [phi, AutomorphicAction.naturality, cd_act, MonObj.comp_mul, cd_mul, GrpObj.comp_inv,
    GrpObj.comp_inv, cd_inv, lift_fst_assoc, lift_fst_assoc, ← Category.assoc,
    MonObj.comp_mul, lift_fst, lift_snd, sub_eq_add_neg]

theorem charValue_inv_mul {T : Over (Spec (CommRingCat.of k))} (g x : T ⟶ E.X) :
    chi q χ x * VectorGroup.charValue χ T ((g * x) ≫ q.hom.hom)⁻¹ =
      VectorGroup.charValue χ T (g ≫ q.hom.hom)⁻¹ := by
  have e1 := charValue_mul_inv χ (g ≫ q.hom.hom)
  have e3 := charValue_mul_inv χ ((g * x) ≫ q.hom.hom)
  have hgx : VectorGroup.charValue χ T ((g * x) ≫ q.hom.hom) = chi q χ g * chi q χ x :=
    chi_mul q χ g x
  rw [hgx] at e3
  linear_combination VectorGroup.charValue χ T (g ≫ q.hom.hom)⁻¹ * e3 -
    (chi q χ x * VectorGroup.charValue χ T ((g * x) ≫ q.hom.hom)⁻¹) * e1

variable (hconj : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X)
    (x : T ⟶ (kernel q).X),
    b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom = g * (x ≫ (kernelι q).hom.hom) * g⁻¹)
  (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
    (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
    b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))
  (hfE : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
    cd ((g * (u ≫ (kernelι q).hom.hom)) ≫ fE) = cd (g ≫ fE) + chi q χ g * cd (u ≫ a.hom.hom))

include hconj hlin hfE in
/-- `Φ` is invariant under right translation of its first variable by the kernel. -/
theorem phi_invariant {T : Over (Spec (CommRingCat.of k))} (g x : T ⟶ E.X)
    (u : T ⟶ (kernel q).X) :
    lift (g * (u ≫ (kernelι q).hom.hom)) x ≫ phi q χ fE = lift g x ≫ phi q χ fE := by
  apply cd_injective
  rw [cd_lift_phi, cd_lift_phi, mul_kernel_comp_q]
  set v := b.act (x⁻¹ ≫ q.hom.hom) u
  have hv : v ≫ (kernelι q).hom.hom = x⁻¹ * (u ≫ (kernelι q).hom.hom) * x := by
    rw [hconj, inv_inv]
  have hgux : g * (u ≫ (kernelι q).hom.hom) * x = (g * x) * (v ≫ (kernelι q).hom.hom) := by
    rw [hv]
    group
  have hva : cd (v ≫ a.hom.hom) = chi q χ x⁻¹ * cd (u ≫ a.hom.hom) := by
    rw [hlin, cd_act]
  have hc : chi q χ (g * x) * chi q χ x⁻¹ = chi q χ g := by
    rw [chi_mul, mul_assoc, chi_mul_inv, mul_one]
  rw [hgux, hfE, hfE, hva]
  linear_combination (VectorGroup.charValue χ T (g ≫ q.hom.hom)⁻¹ * cd (u ≫ a.hom.hom)) * hc

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- The descent `Φ̄ : D ⊗ E → 𝔾ₐ` of `Φ` along `q ▷ E`. -/
def phiBar : (𝔻).X ⊗ E.X ⟶ (𝔾ₐ).X :=
  descendLeft q (phi q χ fE) (fun _ g y u => phi_invariant q a χ b fE hconj hlin hfE g y u)

theorem lift_comp_phiBar {T : Over (Spec (CommRingCat.of k))} (g y : T ⟶ E.X) :
    lift (g ≫ q.hom.hom) y ≫ phiBar q a χ b fE hconj hlin hfE = lift g y ≫ phi q χ fE :=
  lift_comp_descendLeft q _ _ g y

theorem lift_comp_whiskerLeft_phiBar {T Y : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X)
    (w : T ⟶ Y) (t : Y ⟶ E.X) :
    lift (g ≫ q.hom.hom) w ≫ ((𝔻).X ◁ t) ≫ phiBar q a χ b fE hconj hlin hfE =
      lift g (w ≫ t) ≫ phi q χ fE := by
  rw [lift_whiskerLeft_assoc, lift_comp_phiBar]

/-- The integrand identity `Φ̄(z, x y) = Φ̄(z, x) + χ(x) Φ̄(z q(x), y)`. -/
theorem phiBar_mul :
    ((𝔻).X ◁ (fst E.X E.X * snd E.X E.X)) ≫ phiBar q a χ b fE hconj hlin hfE =
      (((𝔻).X ◁ fst E.X E.X) ≫ phiBar q a χ b fE hconj hlin hfE) *
        (lift (fst (𝔻).X (E.X ⊗ E.X) *
            (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)) (snd (𝔻).X (E.X ⊗ E.X)) ≫
          (VectorGroup.weightAction (n := 1) χ).act
            (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)
            (((𝔻).X ◁ snd E.X E.X) ≫ phiBar q a χ b fE hconj hlin hfE)) := by
  apply (cancel_epi (q.hom.hom ▷ (E.X ⊗ E.X))).mp
  apply hom_ext_lift₃
  intro T g x y
  have hL : lift g (lift x y) ≫ (q.hom.hom ▷ (E.X ⊗ E.X)) ≫
      ((𝔻).X ◁ (fst E.X E.X * snd E.X E.X)) ≫ phiBar q a χ b fE hconj hlin hfE =
      lift g (x * y) ≫ phi q χ fE := by
    rw [lift_whiskerRight_assoc, lift_comp_whiskerLeft_phiBar, MonObj.comp_mul, lift_fst,
      lift_snd]
  have hA : lift (g ≫ q.hom.hom) (lift x y) ≫ ((𝔻).X ◁ fst E.X E.X) ≫
      phiBar q a χ b fE hconj hlin hfE = lift g x ≫ phi q χ fE := by
    rw [lift_comp_whiskerLeft_phiBar, lift_fst]
  have hP : lift (g ≫ q.hom.hom) (lift x y) ≫ lift (fst (𝔻).X (E.X ⊗ E.X) *
      (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)) (snd (𝔻).X (E.X ⊗ E.X)) =
      lift ((g * x) ≫ q.hom.hom) (lift x y) := by
    rw [comp_lift, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd,
      MonObj.mul_comp]
  have hB : lift (g ≫ q.hom.hom) (lift x y) ≫ lift (fst (𝔻).X (E.X ⊗ E.X) *
      (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)) (snd (𝔻).X (E.X ⊗ E.X)) ≫
      (VectorGroup.weightAction (n := 1) χ).act
        (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)
        (((𝔻).X ◁ snd E.X E.X) ≫ phiBar q a χ b fE hconj hlin hfE) =
      (VectorGroup.weightAction (n := 1) χ).act (x ≫ q.hom.hom)
        (lift (g * x) y ≫ phi q χ fE) := by
    rw [← Category.assoc, hP, AutomorphicAction.naturality, lift_snd_assoc, lift_fst_assoc,
      lift_comp_whiskerLeft_phiBar, lift_snd]
  rw [hL, lift_whiskerRight_assoc, MonObj.comp_mul, hA, hB]
  apply cd_injective
  rw [cd_mul, cd_act, cd_lift_phi, cd_lift_phi, cd_lift_phi, mul_assoc]
  have hkey := charValue_inv_mul q χ g x
  linear_combination (cd ((g * x) ≫ fE) - cd ((g * (x * y)) ≫ fE)) * hkey

variable [IsAffineHom E.X.hom]

/-- The crossed homomorphism `c' = ∫ Φ̄`, averaged over `D`. -/
def crossedHom : E.X ⟶ (𝔾ₐ).X :=
  DiagonalizableAverage.average Λ (phiBar q a χ b fE hconj hlin hfE)

/-- `c'(x y) = c'(x) + χ(x) c'(y)`. -/
theorem crossedHom_mul :
    (fst E.X E.X * snd E.X E.X) ≫ crossedHom q a χ b fE hconj hlin hfE =
      (fst E.X E.X ≫ crossedHom q a χ b fE hconj hlin hfE) *
        (VectorGroup.weightAction (n := 1) χ).act (fst E.X E.X ≫ q.hom.hom)
          (snd E.X E.X ≫ crossedHom q a χ b fE hconj hlin hfE) := by
  have hR : (VectorGroup.weightAction (n := 1) χ).act (fst E.X E.X ≫ q.hom.hom)
      (snd E.X E.X ≫ crossedHom q a χ b fE hconj hlin hfE) =
      DiagonalizableAverage.average Λ
        (lift (fst (𝔻).X (E.X ⊗ E.X) *
            (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)) (snd (𝔻).X (E.X ⊗ E.X)) ≫
          (VectorGroup.weightAction (n := 1) χ).act
            (snd (𝔻).X (E.X ⊗ E.X) ≫ fst E.X E.X ≫ q.hom.hom)
            (((𝔻).X ◁ snd E.X E.X) ≫ phiBar q a χ b fE hconj hlin hfE)) := by
    rw [DiagonalizableAverage.average_translate, DiagonalizableAverage.average_weightAction,
      crossedHom, DiagonalizableAverage.comp_average_eq]
  rw [hR, crossedHom, DiagonalizableAverage.comp_average_eq,
    DiagonalizableAverage.comp_average_eq, ← DiagonalizableAverage.average_mul, phiBar_mul]

omit [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
  [IsAffineHom E.X.hom] in
theorem isAffineHom_kernel (ha : IsClosedSubgroup a) : IsAffineHom (kernel q).X.hom := by
  have : IsClosedImmersion a.hom.hom.left := ha
  have : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
    infer_instance
  rw [← Over.w a.hom.hom]
  infer_instance

/-- The crossed homomorphism restricts to `a` on the kernel. -/
theorem kernel_comp_crossedHom (ha : IsClosedSubgroup a) :
    (kernelι q).hom.hom ≫ crossedHom q a χ b fE hconj hlin hfE = a.hom.hom := by
  have := isAffineHom_kernel q a ha
  have h : ((𝔻).X ◁ (kernelι q).hom.hom) ≫ phiBar q a χ b fE hconj hlin hfE =
      snd (𝔻).X (kernel q).X ≫ a.hom.hom := by
    apply (cancel_epi (q.hom.hom ▷ (kernel q).X)).mp
    apply hom_ext_lift
    intro T g u
    rw [lift_whiskerRight_assoc, lift_comp_whiskerLeft_phiBar, lift_whiskerRight_assoc,
      lift_snd_assoc]
    apply cd_injective
    rw [cd_lift_phi, hfE]
    have e1 := charValue_mul_inv χ (g ≫ q.hom.hom)
    linear_combination cd (u ≫ a.hom.hom) * e1
  rw [crossedHom, DiagonalizableAverage.comp_average_eq, h, DiagonalizableAverage.average_snd]

end CrossedHom

end Langlands.GroupScheme.LinearAdditiveExtension
