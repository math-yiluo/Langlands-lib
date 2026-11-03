import Langlands.GroupScheme.Dynamic.FlagQuotientAction
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Group structure on an actual normal fpqc coset quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.NormalQuotient

variable {S : Scheme.{u}} (G : GroupScheme S)
variable (H : SubgroupFunctor G) (hn : H.IsNormal)
variable {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T)

include hn hfib

/-- Normality makes the product constant on two quotient fibers. -/
theorem mul_preserves_fibers {T : Over S}
    (a a' b b' : T ⟶ G.X)
    (ha : a ≫ q = a' ≫ q) (hb : b ≫ q = b' ≫ q) :
    (a * b) ≫ q = (a' * b') ≫ q := by
  apply (hfib T _ _).mpr
  have hc := hn T b⁻¹ (a⁻¹ * a') (Subgroup.mem_top _)
    ((hfib T _ _).mp ha)
  have hd := (H.carrier T).mul_mem hc ((hfib T _ _).mp hb)
  simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hd

/-- Normality also makes inverse constant on quotient fibers. -/
theorem inv_preserves_fibers {T : Over S} (a b : T ⟶ G.X)
    (ha : a ≫ q = b ≫ q) : a⁻¹ ≫ q = b⁻¹ ≫ q := by
  apply (hfib T _ _).mpr
  have hc := hn T a (a⁻¹ * b)⁻¹ (Subgroup.mem_top _)
    ((H.carrier T).inv_mem ((hfib T _ _).mp ha))
  simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] using hc

/-- Product compatibility on arbitrary underlying schemes. -/
theorem mul_preserves_scheme_fibers {T : Scheme.{u}}
    (f f' : T ⟶ (G.X ⊗ G.X).left)
    (he : f ≫ (q ⊗ₘ q).left = f' ≫ (q ⊗ₘ q).left) :
    f ≫ (μ[G.X] ≫ q).left = f' ≫ (μ[G.X] ≫ q).left := by
  have hb : f' ≫ (G.X ⊗ G.X).hom = f ≫ (G.X ⊗ G.X).hom := by
    rw [← Over.w (q ⊗ₘ q), ← Category.assoc, ← he, Category.assoc]
  let f₀ : Over.mk (f ≫ (G.X ⊗ G.X).hom) ⟶ G.X ⊗ G.X := Over.homMk f rfl
  let f₁ : Over.mk (f ≫ (G.X ⊗ G.X).hom) ⟶ G.X ⊗ G.X := Over.homMk f' hb
  have he₀ : f₀ ≫ (q ⊗ₘ q) = f₁ ≫ (q ⊗ₘ q) := Over.OverMorphism.ext he
  have ha := congrArg (fun e => e ≫ fst Q Q) he₀
  have hb := congrArg (fun e => e ≫ snd Q Q) he₀
  simp only [Category.assoc, tensorHom_fst] at ha
  simp only [Category.assoc, tensorHom_snd] at hb
  have hm (e : Over.mk (f ≫ (G.X ⊗ G.X).hom) ⟶ G.X ⊗ G.X) :
      e ≫ μ[G.X] = (e ≫ fst _ _) * (e ≫ snd _ _) := by
    rw [Hom.mul_def, lift_comp_fst_snd]
  have hh := mul_preserves_fibers G H hn q hfib
    (f₀ ≫ fst _ _) (f₁ ≫ fst _ _) (f₀ ≫ snd _ _) (f₁ ≫ snd _ _) ha hb
  rw [← hm, ← hm, Category.assoc, Category.assoc] at hh
  exact congrArg (fun e => e.left) hh

/-- Inverse compatibility on arbitrary underlying schemes. -/
theorem inv_preserves_scheme_fibers {T : Scheme.{u}}
    (f f' : T ⟶ G.X.left) (he : f ≫ q.left = f' ≫ q.left) :
    f ≫ (ι[G.X] ≫ q).left = f' ≫ (ι[G.X] ≫ q).left := by
  have hb : f' ≫ G.X.hom = f ≫ G.X.hom := by
    rw [← Over.w q, ← Category.assoc, ← he, Category.assoc]
  let f₀ : Over.mk (f ≫ G.X.hom) ⟶ G.X := Over.homMk f rfl
  let f₁ : Over.mk (f ≫ G.X.hom) ⟶ G.X := Over.homMk f' hb
  have hh := inv_preserves_fibers G H hn q hfib f₀ f₁ (Over.OverMorphism.ext he)
  exact congrArg (fun e => e.left) hh

omit hn hfib

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

variable [QuasiCompact q.left] [Flat q.left] [Surjective q.left]

set_option backward.isDefEq.respectTransparency false in
/-- The product of the quotient projection with itself is an effective epimorphism. -/
theorem effectiveEpi_tensorHom : EffectiveEpi (q ⊗ₘ q).left := by
  have hp : fpqcProperty (q ⊗ₘ q).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w q).symm (Over.w q).symm
  let : QuasiCompact (q ⊗ₘ q).left := hp.1
  let : Flat (q ⊗ₘ q).left := hp.2.1
  let : Surjective (q ⊗ₘ q).left := hp.2.2
  infer_instance

include hn hfib

/-- The multiplication on the quotient, descended as a scheme morphism. -/
def mulSchemeHom : (Q ⊗ Q).left ⟶ Q.left :=
  haveI := effectiveEpi_tensorHom G q
  EffectiveEpi.desc (q ⊗ₘ q).left (μ[G.X] ≫ q).left
    (fun f f' he => mul_preserves_scheme_fibers G H hn q hfib f f' he)

@[reassoc]
theorem fac_mulSchemeHom :
    (q ⊗ₘ q).left ≫ mulSchemeHom G H hn q hfib = (μ[G.X] ≫ q).left :=
  haveI := effectiveEpi_tensorHom G q
  EffectiveEpi.fac _ _ _

/-- The descended multiplication over the original base. -/
def mulHom : Q ⊗ Q ⟶ Q :=
  Over.homMk (mulSchemeHom G H hn q hfib) (by
    have := effectiveEpi_tensorHom G q
    apply (cancel_epi (q ⊗ₘ q).left).mp
    rw [fac_mulSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_mulHom : (q ⊗ₘ q) ≫ mulHom G H hn q hfib = μ[G.X] ≫ q :=
  Over.OverMorphism.ext (fac_mulSchemeHom G H hn q hfib)

/-- The inverse on the quotient, descended as a scheme morphism. -/
def invSchemeHom : Q.left ⟶ Q.left :=
  EffectiveEpi.desc q.left (ι[G.X] ≫ q).left
    (fun f f' he => inv_preserves_scheme_fibers G H hn q hfib f f' he)

@[reassoc]
theorem fac_invSchemeHom :
    q.left ≫ invSchemeHom G H hn q hfib = (ι[G.X] ≫ q).left :=
  EffectiveEpi.fac _ _ _

/-- The descended inverse over the original base. -/
def invHom : Q ⟶ Q :=
  Over.homMk (invSchemeHom G H hn q hfib) (by
    apply (cancel_epi q.left).mp
    rw [fac_invSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_invHom : q ≫ invHom G H hn q hfib = ι[G.X] ≫ q :=
  Over.OverMorphism.ext (fac_invSchemeHom G H hn q hfib)

/-- Multiplication evaluated on arbitrary test points. -/
def mulPoint {T : Over S} (x y : T ⟶ Q) : T ⟶ Q :=
  lift x y ≫ mulHom G H hn q hfib

/-- Inversion evaluated on arbitrary test points. -/
def invPoint {T : Over S} (x : T ⟶ Q) : T ⟶ Q :=
  x ≫ invHom G H hn q hfib

/-- The unit on arbitrary test points is the image of the original unit. -/
def onePoint (T : Over S) : T ⟶ Q := (1 : T ⟶ G.X) ≫ q

theorem mulPoint_lift {T : Over S} (a b : T ⟶ G.X) :
    mulPoint G H hn q hfib (a ≫ q) (b ≫ q) = (a * b) ≫ q := by
  rw [mulPoint, ← lift_map_assoc, fac_mulHom]
  rfl

theorem invPoint_lift {T : Over S} (a : T ⟶ G.X) :
    invPoint G H hn q hfib (a ≫ q) = a⁻¹ ≫ q := by
  rw [invPoint, Category.assoc, fac_invHom]
  rfl

theorem mulPoint_naturality {T V : Over S} (b : V ⟶ T) (x y : T ⟶ Q) :
    b ≫ mulPoint G H hn q hfib x y =
      mulPoint G H hn q hfib (b ≫ x) (b ≫ y) := by
  rw [mulPoint, mulPoint, ← Category.assoc, comp_lift]

theorem invPoint_naturality {T V : Over S} (b : V ⟶ T) (x : T ⟶ Q) :
    b ≫ invPoint G H hn q hfib x = invPoint G H hn q hfib (b ≫ x) :=
  (Category.assoc _ _ _).symm

omit hn hfib [QuasiCompact q.left] [Flat q.left] [Surjective q.left] in
theorem onePoint_naturality {T V : Over S} (b : V ⟶ T) :
    b ≫ onePoint G q T = onePoint G q V := by
  rw [onePoint, onePoint, ← Category.assoc, MonObj.comp_one]

theorem one_mulPoint {T : Over S} (x : T ⟶ Q) :
    mulPoint G H hn q hfib (onePoint G q T) x = x := by
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q x
  intro V b a hb
  rw [mulPoint_naturality, onePoint_naturality, hb, onePoint, mulPoint_lift, one_mul]

theorem mulPoint_one {T : Over S} (x : T ⟶ Q) :
    mulPoint G H hn q hfib x (onePoint G q T) = x := by
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q x
  intro V b a hb
  rw [mulPoint_naturality, onePoint_naturality, hb, onePoint, mulPoint_lift, mul_one]

theorem mulPoint_assoc {T : Over S} (x y z : T ⟶ Q) :
    mulPoint G H hn q hfib (mulPoint G H hn q hfib x y) z =
      mulPoint G H hn q hfib x (mulPoint G H hn q hfib y z) := by
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q x
  intro V b a hb
  simp only [mulPoint_naturality, hb]
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q (b ≫ y)
  intro W c a' hc
  simp only [mulPoint_naturality, hc, ← Category.assoc]
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q ((c ≫ b) ≫ z)
  intro Z d a'' hd
  simp only [mulPoint_naturality, hd, ← Category.assoc]
  simp only [mulPoint_lift, mul_assoc]

theorem inv_mulPoint {T : Over S} (x : T ⟶ Q) :
    mulPoint G H hn q hfib (invPoint G H hn q hfib x) x = onePoint G q T := by
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q x
  intro V b a hb
  rw [mulPoint_naturality, invPoint_naturality, hb, invPoint_lift,
    mulPoint_lift, inv_mul_cancel, onePoint_naturality, onePoint]

theorem mulPoint_inv {T : Over S} (x : T ⟶ Q) :
    mulPoint G H hn q hfib x (invPoint G H hn q hfib x) = onePoint G q T := by
  apply Dynamic.flagQuotient_hom_ext_of_local_lift G q x
  intro V b a hb
  rw [mulPoint_naturality, invPoint_naturality, hb, invPoint_lift,
    mulPoint_lift, mul_inv_cancel, onePoint_naturality, onePoint]

/-- The actual quotient scheme has the descended group structure. -/
@[instance_reducible]
def groupObj : GrpObj Q where
  one := η[G.X] ≫ q
  mul := mulHom G H hn q hfib
  inv := invHom G H hn q hfib
  one_mul := by
    have hp : lift (onePoint G q (𝟙_ (Over S) ⊗ Q)) (snd _ _) =
        (η[G.X] ≫ q) ▷ Q := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, whiskerRight_fst, onePoint, Hom.one_def, Category.assoc]
        exact congrArg (fun f => f ≫ η[G.X] ≫ q) (toUnit_unique _ _)
      · simp only [lift_snd, whiskerRight_snd]
    rw [← hp, leftUnitor_hom]
    exact one_mulPoint G H hn q hfib (snd _ _)
  mul_one := by
    have hp : lift (fst _ _) (onePoint G q (Q ⊗ 𝟙_ (Over S))) =
        Q ◁ (η[G.X] ≫ q) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, whiskerLeft_fst]
      · simp only [lift_snd, whiskerLeft_snd, onePoint, Hom.one_def, Category.assoc]
        exact congrArg (fun f => f ≫ η[G.X] ≫ q) (toUnit_unique _ _)
    rw [← hp, rightUnitor_hom]
    exact mulPoint_one G H hn q hfib (fst _ _)
  mul_assoc := by
    let x := fst (Q ⊗ Q) Q ≫ fst Q Q
    let y := fst (Q ⊗ Q) Q ≫ snd Q Q
    let z := snd (Q ⊗ Q) Q
    have hp : lift x y = fst (Q ⊗ Q) Q := by
      dsimp [x, y]
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    have hl : lift (mulPoint G H hn q hfib x y) z = mulHom G H hn q hfib ▷ Q := by
      rw [mulPoint, hp]
      dsimp [z]
      rw [← lift_whiskerRight, lift_fst_snd, Category.id_comp]
    have ha : lift x (lift y z) = (α_ Q Q Q).hom := by
      dsimp [x, y, z]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, associator_hom_fst]
      · apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst, associator_hom_snd_fst]
        · simp only [Category.assoc, lift_snd, associator_hom_snd_snd]
    have e := mulPoint_assoc G H hn q hfib x y z
    change lift (mulPoint G H hn q hfib x y) z ≫ mulHom G H hn q hfib =
      lift x (lift y z ≫ mulHom G H hn q hfib) ≫ mulHom G H hn q hfib at e
    rw [hl, ← lift_whiskerLeft_assoc, ha] at e
    exact e
  left_inv := by
    simpa only [mulPoint, invPoint, onePoint, Category.id_comp,
      Hom.one_def, Category.assoc] using inv_mulPoint G H hn q hfib (𝟙 Q)
  right_inv := by
    simpa only [mulPoint, invPoint, onePoint, Category.id_comp,
      Hom.one_def, Category.assoc] using mulPoint_inv G H hn q hfib (𝟙 Q)

/-- The quotient with its actual descended structure. -/
abbrev groupScheme : GroupScheme S :=
  letI := groupObj G H hn q hfib
  Grp.mk Q

/-- The given scheme projection preserves unit and multiplication. -/
theorem isMonHom :
    letI := groupObj G H hn q hfib
    IsMonHom q := by
  letI := groupObj G H hn q hfib
  exact ⟨rfl, (fac_mulHom G H hn q hfib).symm⟩

/-- The quotient projection as a group-scheme homomorphism. -/
def hom : G ⟶ groupScheme G H hn q hfib :=
  letI := groupObj G H hn q hfib
  letI : IsMonHom q := isMonHom G H hn q hfib
  Grp.homMk q

/-- The group-scheme projection retains the original scheme morphism. -/
theorem hom_hom : (hom G H hn q hfib).hom.hom = q := rfl

/-- The represented kernel is exactly the specified all-test subgroup functor. -/
theorem range_kernel :
    SubgroupFunctor.range (kernelι (hom G H hn q hfib)) = H := by
  letI := groupObj G H hn q hfib
  letI : IsMonHom q := isMonHom G H hn q hfib
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  change (∃ y, y ≫ (kernelι (hom G H hn q hfib)).hom.hom = x) ↔ x ∈ H.carrier T
  have hk : x ≫ q = (1 : T ⟶ Q) ↔ x ∈ H.carrier T := by
    change x ≫ q = (1 : T ⟶ G.X) ≫ q ↔ _
    rw [eq_comm, hfib]
    simp only [inv_one, one_mul]
  constructor
  · rintro ⟨y, rfl⟩
    apply hk.mp
    have hy := (kernelPointsEquiv (hom G H hn q hfib) T y).property
    exact hy
  · intro hx
    refine ⟨(kernel_isPullback (hom G H hn q hfib)).lift x (toUnit T) (hk.mpr hx), ?_⟩
    exact (kernel_isPullback (hom G H hn q hfib)).lift_fst _ _ _

/-- A locally finitely presented fpqc coset map gives the exact published
represented fppf group quotient. -/
theorem isFppfQuotient [LocallyOfFinitePresentation q.left] :
    RelativeRoot.IsFppfQuotient H (hom G H hn q hfib) :=
  ⟨(inferInstance : Flat q.left), (inferInstance : Surjective q.left),
    (inferInstance : LocallyOfFinitePresentation q.left), range_kernel G H hn q hfib⟩

end Langlands.GroupScheme.NormalQuotient
