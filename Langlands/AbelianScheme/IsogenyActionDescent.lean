import Langlands.AbelianScheme.IsogenyFactorization
import Langlands.AbelianScheme.FiniteEtaleQuotient
import Langlands.AbelianScheme.LieOrderBaseChange

/-! # Descent of integral actions through actual isogenies -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}} {A B C : AbelianScheme S}

/-- A homomorphism vanishes on the actual scheme kernel of `q`. -/
def KillsKernel (q : A ⟶ B) (g : A ⟶ C) : Prop :=
  GroupScheme.kernelι (groupHom q) ≫ groupHom g = 1

/-- The defining kernel square makes the original homomorphism vanish on its kernel. -/
theorem killsKernel_self (q : A ⟶ B) : KillsKernel q q := by
  apply Grp.hom_ext
  exact (GroupScheme.kernel_isPullback (groupHom q)).w

/-- Any actual homomorphism factoring through `q` vanishes on its scheme kernel. -/
theorem killsKernel_of_factor (q : A ⟶ B) (d : B ⟶ C) :
    KillsKernel q (q ≫ d) := by
  change GroupScheme.kernelι (groupHom q) ≫ (groupHom q ≫ groupHom d) = 1
  rw [← Category.assoc, killsKernel_self q]
  exact MonObj.one_comp _

namespace IsogenyActionDescent

variable {q : A ⟶ B} (hq : IsIsogeny q)

/-- Factor a kernel-killing homomorphism through a supplied isogeny. -/
def lift (g : A ⟶ C) (hg : KillsKernel q g) : B ⟶ C :=
  Additive.ofMul (GroupScheme.IsogenyFactorization.lift hq (groupHom g) hg)

@[reassoc]
theorem fac (g : A ⟶ C) (hg : KillsKernel q g) : q ≫ lift hq g hg = g :=
  congrArg Additive.ofMul (GroupScheme.IsogenyFactorization.fac hq (groupHom g) hg)

include hq in
/-- Cancellation is valid for actual abelian homomorphisms out of an isogeny target. -/
theorem hom_ext (a b : B ⟶ C) (h : q ≫ a = q ≫ b) : a = b :=
  congrArg Additive.ofMul (GroupScheme.IsogenyFactorization.hom_ext hq
    (groupHom a) (groupHom b) (congrArg Additive.toMul h))

theorem lift_unique (g : A ⟶ C) (hg : KillsKernel q g) (d : B ⟶ C)
    (hd : q ≫ d = g) : d = lift hq g hg :=
  hom_ext hq d _ (hd.trans (fac hq g hg).symm)

include hq in
/-- Pullback preserves vanishing on the scheme kernel, by the descended factorization. -/
theorem killsKernel_baseChange (g : A ⟶ C) (hg : KillsKernel q g) (b : T ⟶ S) :
    KillsKernel ((baseChange b).map q) ((baseChange b).map g) := by
  rw [← fac hq g hg, Functor.map_comp]
  exact killsKernel_of_factor _ _

/-- The unique factorization commutes with arbitrary scheme base change. -/
theorem lift_baseChange (g : A ⟶ C) (hg : KillsKernel q g) (b : T ⟶ S) :
    (baseChange b).map (lift hq g hg) =
      lift (hq.baseChange b) ((baseChange b).map g)
        (killsKernel_baseChange hq g hg b) := by
  apply lift_unique
  rw [← Functor.map_comp, fac]

variable {R : Type v} [Ring R] (α : R →+* End A)
  (hα : ∀ r, KillsKernel q (α r ≫ q))

/-- Descend a unital integral action preserving the actual isogeny kernel. -/
def action : R →+* End B where
  toFun r := lift hq (α r ≫ q) (hα r)
  map_one' := by
    apply hom_ext hq
    rw [fac, map_one]
    rfl
  map_zero' := by
    apply hom_ext hq
    rw [fac, map_zero, zero_comp, comp_zero]
  map_add' r s := by
    apply hom_ext hq
    rw [fac, map_add, Preadditive.add_comp, Preadditive.comp_add, fac, fac]
  map_mul' r s := by
    apply hom_ext hq
    change q ≫ lift hq (α (r * s) ≫ q) (hα (r * s)) =
      q ≫ (lift hq (α s ≫ q) (hα s) ≫ lift hq (α r ≫ q) (hα r))
    rw [fac, map_mul]
    change (α s ≫ α r) ≫ q = _
    rw [← Category.assoc, fac]
    simp only [Category.assoc, fac]

@[reassoc]
theorem action_fac (r : R) : q ≫ action hq α hα r = α r ≫ q :=
  fac hq _ _

/-- Equivariance of `q` uniquely determines the descended action. -/
theorem action_unique (β : R →+* End B)
    (hβ : ∀ r, q ≫ β r = α r ≫ q) : β = action hq α hα := by
  ext r
  exact hom_ext hq _ _ ((hβ r).trans (action_fac hq α hα r).symm)

include hq hα in
/-- The pulled-back action preserves the pulled-back actual scheme kernel. -/
theorem action_killsKernel_baseChange (b : T ⟶ S) (r : R) :
    KillsKernel ((baseChange b).map q)
      (baseChangeOrderAction b A α r ≫ (baseChange b).map q) := by
  change KillsKernel ((baseChange b).map q)
    ((baseChange b).map (α r) ≫ (baseChange b).map q)
  rw [← Functor.map_comp]
  exact killsKernel_baseChange hq _ (hα r) b

/-- Descent of an actual ring action commutes with every scheme base change. -/
theorem action_baseChange (b : T ⟶ S) :
    baseChangeOrderAction b B (action hq α hα) =
      action (hq.baseChange b) (baseChangeOrderAction b A α)
        (action_killsKernel_baseChange hq α hα b) := by
  apply action_unique
  intro r
  change (baseChange b).map q ≫ (baseChange b).map (action hq α hα r) = _
  rw [← Functor.map_comp, action_fac, Functor.map_comp]
  rfl

end IsogenyActionDescent

namespace FiniteEtaleSubgroup

variable (K : FiniteEtaleSubgroup A)

/-- An actual endomorphism preserves the supplied subgroup if it restricts to it. -/
def PreservedBy (e : End A) : Prop :=
  ∃ k : CommGroupScheme.End K.G, K.inclusion ≫ commHom e = k ≫ K.inclusion

namespace QuotientData

variable {K : FiniteEtaleSubgroup A} (D : K.QuotientData)

/-- Vanishing on the supplied subgroup is equivalent to vanishing on the scheme kernel. -/
theorem killsKernel_iff (g : A ⟶ C) :
    KillsKernel D.q g ↔ K.inclusion ≫ commHom g = 0 := by
  constructor
  · intro hg
    change CommGroupScheme.groupHom K.inclusion ≫ groupHom g = 1
    rw [← D.kernelIso_hom_inclusion, Category.assoc, hg]
    exact MonObj.comp_one _
  · intro hg
    change GroupScheme.kernelι (groupHom D.q) ≫ groupHom g = 1
    apply (cancel_epi D.kernelIso.hom).mp
    rw [← Category.assoc, D.kernelIso_hom_inclusion]
    change CommGroupScheme.groupHom (K.inclusion ≫ commHom g) = D.kernelIso.hom ≫ 1
    rw [hg]
    exact (MonObj.comp_one D.kernelIso.hom).symm

@[reassoc (attr := simp)]
theorem inclusion_comp_q : K.inclusion ≫ commHom D.q = 0 :=
  (D.killsKernel_iff D.q).mp (killsKernel_self D.q)

/-- Restriction to the actual subgroup suffices for kernel preservation. -/
theorem killsKernel_of_preserved {e : End A} (he : K.PreservedBy e) :
    KillsKernel D.q (e ≫ D.q) := by
  apply (D.killsKernel_iff _).mpr
  obtain ⟨k, hk⟩ := he
  change K.inclusion ≫ (commHom e ≫ commHom D.q) = 0
  rw [← Category.assoc, hk, Category.assoc, inclusion_comp_q, comp_zero]

/-- The quotient's universal factorization for a supplied subgroup-killing map. -/
def lift (g : A ⟶ C) (hg : K.inclusion ≫ commHom g = 0) : D.B ⟶ C :=
  IsogenyActionDescent.lift D.isIsogeny g ((D.killsKernel_iff g).mpr hg)

@[reassoc]
theorem fac_lift (g : A ⟶ C) (hg : K.inclusion ≫ commHom g = 0) :
    D.q ≫ D.lift g hg = g := IsogenyActionDescent.fac D.isIsogeny _ _

variable {R : Type v} [Ring R] (α : R →+* End A)
  (hα : ∀ r, K.PreservedBy (α r))

/-- The actual quotient inherits any unital integral action preserving its subgroup. -/
def action : R →+* End D.B :=
  IsogenyActionDescent.action D.isIsogeny α (fun r => D.killsKernel_of_preserved (hα r))

@[reassoc]
theorem action_fac (r : R) : D.q ≫ D.action α hα r = α r ≫ D.q :=
  IsogenyActionDescent.action_fac _ _ _ _

/-- Equivariance determines the quotient action uniquely. -/
theorem action_unique (β : R →+* End D.B)
    (hβ : ∀ r, D.q ≫ β r = α r ≫ D.q) : β = D.action α hα :=
  IsogenyActionDescent.action_unique _ _ _ β hβ

/-- Pulling back the quotient action equals descent through the pulled-back quotient map. -/
theorem action_baseChange (b : T ⟶ S) :
    baseChangeOrderAction b D.B (D.action α hα) =
      IsogenyActionDescent.action (D.isIsogeny.baseChange b) (baseChangeOrderAction b A α)
        (IsogenyActionDescent.action_killsKernel_baseChange D.isIsogeny α
          (fun r => D.killsKernel_of_preserved (hα r)) b) :=
  IsogenyActionDescent.action_baseChange _ _ _ b

end QuotientData
end FiniteEtaleSubgroup
end Langlands.AbelianScheme
