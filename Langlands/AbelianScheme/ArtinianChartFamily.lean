import Langlands.AbelianScheme.ArtinianLiftAssembly
import Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

/-! # Charts by opens of a model over the thicker ring, and lifts of their transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.TwistedOpenGluing
open Langlands.AlgebraicGeometry.SquareZeroAffinePairs
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections
open Langlands.AlgebraicGeometry.Deformation.ElementaryIdealCoefficients
open Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] (S : Setting R' R)

/-- A scheme over the thicker ring, with a chosen base change to the thinner ring and a chosen
residue fibre of that base change. -/
structure Model where
  Y : Over (Spec (CommRingCat.of R'))
  YS : Scheme.{u}
  q : YS ⟶ Y.left
  pS : YS ⟶ Spec (CommRingCat.of R)
  isPullback_q : IsPullback q pS Y.hom S.t
  E : Scheme.{u}
  iE : E ⟶ YS
  pE : E ⟶ Spec (CommRingCat.of (ResidueField R'))
  isPullback_iE : IsPullback iE pE pS S.c

namespace Model

variable {S} (M : S.Model)

/-- The base change of an open of the model. -/
abbrev VT (U : M.Y.left.Opens) : M.YS.Opens := M.q ⁻¹ᵁ U

/-- The base change map from an open of the base change which is the preimage of an open of the
model. -/
abbrev resTo (U : M.Y.left.Opens) (V' : M.YS.Opens) (hV : V' = M.VT U) :
    V'.toScheme ⟶ U.toScheme :=
  M.q.resLE U V' hV.le

theorem isPullback_resTo (U : M.Y.left.Opens) (V' : M.YS.Opens) (hV : V' = M.VT U) :
    IsPullback (M.resTo U V' hV) (V'.ι ≫ M.pS) (U.ι ≫ M.Y.hom) S.t := by
  subst hV
  rw [resTo, Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict M.q U).paste_vert M.isPullback_q

/-- A map into an open of the model lying over the thinner ring factors through the base change
of the open. -/
def liftVT {U : M.Y.left.Opens} {V' : M.YS.Opens} (hV : V' = M.VT U) {T : Scheme.{u}}
    (g : T ⟶ U.toScheme) (v : T ⟶ Spec (CommRingCat.of R)) (h : g ≫ U.ι ≫ M.Y.hom = v ≫ S.t) :
    T ⟶ V'.toScheme :=
  (M.isPullback_resTo U V' hV).lift g v h

@[reassoc (attr := simp)]
theorem liftVT_res {U : M.Y.left.Opens} {V' : M.YS.Opens} (hV : V' = M.VT U) {T : Scheme.{u}}
    (g : T ⟶ U.toScheme) (v : T ⟶ Spec (CommRingCat.of R)) (h : g ≫ U.ι ≫ M.Y.hom = v ≫ S.t) :
    M.liftVT hV g v h ≫ M.resTo U V' hV = g :=
  (M.isPullback_resTo U V' hV).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem liftVT_pS {U : M.Y.left.Opens} {V' : M.YS.Opens} (hV : V' = M.VT U) {T : Scheme.{u}}
    (g : T ⟶ U.toScheme) (v : T ⟶ Spec (CommRingCat.of R)) (h : g ≫ U.ι ≫ M.Y.hom = v ≫ S.t) :
    M.liftVT hV g v h ≫ V'.ι ≫ M.pS = v :=
  (M.isPullback_resTo U V' hV).lift_snd _ _ _

@[reassoc]
theorem resTo_ι (U : M.Y.left.Opens) (V' : M.YS.Opens) (hV : V' = M.VT U) :
    M.resTo U V' hV ≫ U.ι = V'.ι ≫ M.q :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc]
theorem resTo_over (U : M.Y.left.Opens) (V' : M.YS.Opens) (hV : V' = M.VT U) :
    M.resTo U V' hV ≫ U.ι ≫ M.Y.hom = (V'.ι ≫ M.pS) ≫ S.t :=
  (M.isPullback_resTo U V' hV).w

@[reassoc]
theorem resTo_homOfLE {U U' : M.Y.left.Opens} (h : U ≤ U') {V' V'' : M.YS.Opens}
    (hV : V' = M.VT U) (hV' : V'' = M.VT U') (h' : V' ≤ V'') :
    M.resTo U V' hV ≫ M.Y.left.homOfLE h = M.YS.homOfLE h' ≫ M.resTo U' V'' hV' := by
  rw [Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]

/-- Maps from an affine open of the model agreeing after base change to the thinner ring agree
modulo the kernel. -/
theorem agreeMod_of_resTo {U : M.Y.left.Opens} (hU : IsAffineOpen U) {V' : M.YS.Opens}
    (hV : V' = M.VT U) {T : Scheme.{u}} {a b : U.toScheme ⟶ T}
    (h : M.resTo U V' hV ≫ a = M.resTo U V' hV ≫ b) :
    AgreeMod (RingHom.ker S.φ) hU a b := by
  let J := Extended (RingHom.ker S.φ) (Sections M.Y U)
  let f : R' →+* Sections M.Y U ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap R' (Sections M.Y U))
  have hf : RingHom.ker S.φ ≤ RingHom.ker f := fun x hx ↦ by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  let g : R →+* Sections M.Y U ⧸ J := RingHom.liftOfSurjective S.φ S.surj ⟨f, hf⟩
  have hg : g.comp S.φ = f := by
    ext x
    exact RingHom.liftOfSurjective_comp_apply S.φ S.surj ⟨f, hf⟩ x
  let u := specMap (Ideal.Quotient.mk J) ≫ hU.isoSpec.inv
  have hu : u ≫ U.ι ≫ M.Y.hom = specMap g ≫ S.t := by
    have e : hU.isoSpec.inv ≫ U.ι ≫ M.Y.hom = str M.Y U := by
      rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι, fromSpec_hom hU]
    change (specMap (Ideal.Quotient.mk J) ≫ hU.isoSpec.inv) ≫ U.ι ≫ M.Y.hom =
      specMap g ≫ specMap S.φ
    rw [Category.assoc, e, ← specMap_comp, ← specMap_comp, hg]
  have hw := M.liftVT_res hV u (specMap g) hu
  unfold AgreeMod
  change u ≫ a = u ≫ b
  rw [← hw, Category.assoc, h, ← Category.assoc]

/-- Maps from an affine open of the model agreeing modulo the kernel agree after base change to
the thinner ring. -/
theorem resTo_eq_of_agreeMod {U : M.Y.left.Opens} (hU : IsAffineOpen U) {V' : M.YS.Opens}
    (hV : V' = M.VT U) {T : Scheme.{u}} {a b : U.toScheme ⟶ T}
    (h : AgreeMod (RingHom.ker S.φ) hU a b) :
    M.resTo U V' hV ≫ a = M.resTo U V' hV ≫ b := by
  refine comp_eq_of_agreeMod hU h (M.resTo U V' hV)
    (V'.ι ≫ M.pS ≫ specMap (RingHom.kerLift S.φ)) ?_
  have hφ : S.φ = (RingHom.kerLift S.φ).comp (Ideal.Quotient.mk _) := by
    ext x
    exact (RingHom.kerLift_mk S.φ x).symm
  have ht : S.t = specMap (RingHom.kerLift S.φ) ≫
      specMap (Ideal.Quotient.mk (RingHom.ker S.φ)) := by
    rw [← specMap_comp]
    exact congrArg specMap hφ
  rw [M.resTo_over, ht]
  simp only [Category.assoc]

end Model

section Charts

variable {S} (M : S.Model) (X : Over (Spec (CommRingCat.of R))) (e : M.E ⟶ X.left)

/-- A finite family of charts of `X` by the base changes of affine opens of the model, agreeing
with `e` on the residue fibre and lying over the thinner ring. -/
structure ChartFamily where
  L : Type u
  [fintype : Fintype L]
  V : L → M.Y.left.Opens
  affine : ∀ l, IsAffineOpen (V l)
  κ : ∀ l, (M.VT (V l)).toScheme ⟶ X.left
  [isOpenImmersion : ∀ l, IsOpenImmersion (κ l)]
  κ_base : ∀ l, κ l ≫ X.hom = (M.VT (V l)).ι ≫ M.pS
  fibre : ∀ l, M.iE.resLE (M.VT (V l)) (M.iE ⁻¹ᵁ M.VT (V l)) le_rfl ≫ κ l =
    (M.iE ⁻¹ᵁ M.VT (V l)).ι ≫ e

attribute [instance] ChartFamily.fintype ChartFamily.isOpenImmersion

namespace ChartFamily

variable {M X e} (K : ChartFamily M X e)

/-- A chart agrees with `e` on every map factoring through the residue fibre. -/
theorem κ_comp_of_fibre (l : K.L) {T : Scheme.{u}} (g : T ⟶ (M.VT (K.V l)).toScheme)
    (h : T ⟶ M.E) (hg : g ≫ (M.VT (K.V l)).ι = h ≫ M.iE) : g ≫ K.κ l = h ≫ e := by
  have hr : Set.range h ⊆ Set.range (M.iE ⁻¹ᵁ M.VT (K.V l)).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change M.iE (h x) ∈ M.VT (K.V l)
    rw [← Scheme.Hom.comp_apply, ← hg, Scheme.Hom.comp_apply]
    exact (g x).2
  let h' := IsOpenImmersion.lift (M.iE ⁻¹ᵁ M.VT (K.V l)).ι h hr
  have hh' : h' ≫ (M.iE ⁻¹ᵁ M.VT (K.V l)).ι = h := IsOpenImmersion.lift_fac _ _ _
  have hg' : g = h' ≫ M.iE.resLE (M.VT (K.V l)) (M.iE ⁻¹ᵁ M.VT (K.V l)) le_rfl := by
    rw [← cancel_mono (M.VT (K.V l)).ι, hg, Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, hh']
  rw [hg', Category.assoc, K.fibre, ← Category.assoc, hh']

theorem κ_apply (l : K.L) (x : (M.VT (K.V l)).toScheme) (y : M.E)
    (hy : M.iE y = (M.VT (K.V l)).ι x) : K.κ l x = e y := by
  have hy' : y ∈ M.iE ⁻¹ᵁ M.VT (K.V l) := by
    change M.iE y ∈ M.VT (K.V l)
    rw [hy]
    exact x.2
  let y' : (M.iE ⁻¹ᵁ M.VT (K.V l)).toScheme := ⟨y, hy'⟩
  have hx : M.iE.resLE (M.VT (K.V l)) (M.iE ⁻¹ᵁ M.VT (K.V l)) le_rfl y' = x := by
    apply (M.VT (K.V l)).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    exact hy
  rw [← hx, ← Scheme.Hom.comp_apply, K.fibre, Scheme.Hom.comp_apply]
  rfl

variable [IsArtinianRing R] [IsLocalRing R]

omit [IsLocalRing R'] in
instance surjective_iE : Surjective M.iE := by
  have := S.c_surjective
  exact MorphismProperty.of_isPullback (P := @Surjective) M.isPullback_iE.flip inferInstance

theorem κ_apply_eq (l m : K.L) (x : (M.VT (K.V l)).toScheme) (x' : (M.VT (K.V m)).toScheme)
    (h : (M.VT (K.V l)).ι x = (M.VT (K.V m)).ι x') : K.κ l x = K.κ m x' := by
  obtain ⟨y, hy⟩ := M.iE.surjective ((M.VT (K.V l)).ι x)
  rw [K.κ_apply l x y hy, K.κ_apply m x' y (hy.trans h)]

theorem range_homOfLE_κ (l m : K.L) :
    Set.range (M.YS.homOfLE (inf_le_right : M.VT (K.V l) ⊓ M.VT (K.V m) ≤ _) ≫ K.κ m) ⊆
      Set.range (K.κ l) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨M.YS.homOfLE (inf_le_left : M.VT (K.V l) ⊓ M.VT (K.V m) ≤ _) y, ?_⟩
  rw [Scheme.Hom.comp_apply]
  apply K.κ_apply_eq
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

/-- The transition from chart `m` to chart `l` on their overlap. -/
def lift (l m : K.L) :
    (M.VT (K.V l) ⊓ M.VT (K.V m)).toScheme ⟶ (M.VT (K.V l)).toScheme :=
  IsOpenImmersion.lift (K.κ l) (M.YS.homOfLE inf_le_right ≫ K.κ m) (K.range_homOfLE_κ l m)

@[reassoc (attr := simp)]
theorem lift_κ (l m : K.L) : K.lift l m ≫ K.κ l = M.YS.homOfLE inf_le_right ≫ K.κ m :=
  IsOpenImmersion.lift_fac _ _ _

/-- The transition maps of the charts, as morphisms into the base change of the model. -/
def θS (l m : K.L) : (M.VT (K.V l) ⊓ M.VT (K.V m)).toScheme ⟶ M.YS :=
  K.lift l m ≫ (M.VT (K.V l)).ι

theorem lift_eq_homOfLE_apply (l m : K.L) (y : (M.VT (K.V l) ⊓ M.VT (K.V m)).toScheme) :
    K.lift l m y = M.YS.homOfLE inf_le_left y := by
  apply (K.κ l).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, lift_κ, Scheme.Hom.comp_apply]
  apply K.κ_apply_eq
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

theorem θS_pointwise (l m : K.L) : IsPointwiseInclusion (K.θS l m) := by
  intro y
  rw [θS, Scheme.Hom.comp_apply, K.lift_eq_homOfLE_apply, ← Scheme.Hom.comp_apply,
    Scheme.homOfLE_ι]

theorem θS_self (l : K.L) : K.θS l l = (M.VT (K.V l) ⊓ M.VT (K.V l)).ι := by
  have : K.lift l l = M.YS.homOfLE inf_le_left :=
    (IsOpenImmersion.lift_uniq _ _ _ (M.YS.homOfLE inf_le_left) rfl).symm
  unfold θS
  rw [this, Scheme.homOfLE_ι]

theorem θS_base (l m : K.L) :
    K.θS l m ≫ M.pS = (M.VT (K.V l) ⊓ M.VT (K.V m)).ι ≫ M.pS := by
  rw [θS, Category.assoc, ← K.κ_base, lift_κ_assoc, K.κ_base, Scheme.homOfLE_ι_assoc]

/-- On the residue fibre the transition maps are the inclusions. -/
theorem θS_fibre (l m : K.L) {T : Scheme.{u}} (g : T ⟶ (M.VT (K.V l) ⊓ M.VT (K.V m)).toScheme)
    (h : T ⟶ M.E) (hg : g ≫ (M.VT (K.V l) ⊓ M.VT (K.V m)).ι = h ≫ M.iE) :
    g ≫ K.θS l m = g ≫ (M.VT (K.V l) ⊓ M.VT (K.V m)).ι := by
  have h₁ := K.κ_comp_of_fibre m (g ≫ M.YS.homOfLE inf_le_right) h
    (by rw [Category.assoc, Scheme.homOfLE_ι, hg])
  have h₂ := K.κ_comp_of_fibre l (g ≫ M.YS.homOfLE inf_le_left) h
    (by rw [Category.assoc, Scheme.homOfLE_ι, hg])
  have e₁ : g ≫ K.lift l m = g ≫ M.YS.homOfLE inf_le_left := by
    rw [← cancel_mono (K.κ l)]
    simp only [Category.assoc] at h₁ h₂ ⊢
    rw [lift_κ, h₁, h₂]
  rw [θS, ← Category.assoc, e₁, Category.assoc, Scheme.homOfLE_ι]

theorem θS_cocycle (l m n : K.L) :
    restrictTo (K.θS m n) (K.θS_pointwise m n)
        (W := M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ K.θS l m =
      M.YS.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n) ≤ M.VT (K.V l) ⊓ M.VT (K.V n)) ≫
        K.θS l n := by
  have h₁ : restrictTo (K.θS m n) (K.θS_pointwise m n)
        (W := M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫
          M.YS.homOfLE (inf_le_right : M.VT (K.V l) ⊓ M.VT (K.V m) ≤ _) =
      M.YS.homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n) ≤ M.VT (K.V m) ⊓ M.VT (K.V n)) ≫
        K.lift m n := by
    rw [← cancel_mono (M.VT (K.V m)).ι, Category.assoc, Scheme.homOfLE_ι, restrictTo_ι,
      Category.assoc]
    rfl
  have h₂ : restrictTo (K.θS m n) (K.θS_pointwise m n)
        (W := M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ K.lift l m =
      M.YS.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n) ≤ M.VT (K.V l) ⊓ M.VT (K.V n)) ≫
        K.lift l n := by
    rw [← cancel_mono (K.κ l), Category.assoc, lift_κ, reassoc_of% h₁, lift_κ, Category.assoc,
      lift_κ, Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc]
  rw [show K.θS l m = K.lift l m ≫ (M.VT (K.V l)).ι from rfl,
    show K.θS l n = K.lift l n ≫ (M.VT (K.V l)).ι from rfl, reassoc_of% h₂]

end ChartFamily

end Charts

section Lifts

variable {S} {M : S.Model} {X : Over (Spec (CommRingCat.of R))} {e : M.E ⟶ X.left}

theorem c_t : S.c ≫ S.t = specMap (residue R') := by
  rw [show S.c = specMap S.ψ from rfl, show S.t = specMap S.φ from rfl, ← specMap_comp, S.hψ]

namespace Model

variable (M)

instance surjective_q [IsArtinianRing R'] [Nontrivial R] : Surjective M.q := by
  have : Surjective S.t := by
    have := primeSpectrum_subsingleton (R := R')
    constructor
    intro y
    obtain ⟨x⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    exact ⟨x, @Subsingleton.elim (PrimeSpectrum R') ‹_› _ _⟩
  exact MorphismProperty.of_isPullback (P := @Surjective) M.isPullback_q.flip inferInstance

end Model

namespace ChartFamily

variable (K : ChartFamily M X e)

/-- The base change map of a double overlap. -/
abbrev res₂ (l m : K.L) :
    (M.VT (K.V l) ⊓ M.VT (K.V m)).toScheme ⟶ (K.V l ⊓ K.V m).toScheme :=
  M.resTo (K.V l ⊓ K.V m) (M.VT (K.V l) ⊓ M.VT (K.V m)) (Scheme.Hom.preimage_inf _).symm

/-- The base change map of a triple overlap. -/
abbrev res₃ (l m n : K.L) :
    (M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n)).toScheme ⟶
      (K.V l ⊓ K.V m ⊓ K.V n).toScheme :=
  M.resTo (K.V l ⊓ K.V m ⊓ K.V n) (M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n))
    (by simp only [Model.VT, Scheme.Hom.preimage_inf])

variable [IsArtinianRing R] [IsLocalRing R]

/-- Lifts of the transition maps of the charts to the model over the thicker ring. -/
structure Lifts where
  θ : ∀ l m, (K.V l ⊓ K.V m).toScheme ⟶ M.Y.left
  overBase : ∀ l m, θ l m ≫ M.Y.hom = (K.V l ⊓ K.V m).ι ≫ M.Y.hom
  reduces : ∀ l m, K.res₂ l m ≫ θ l m = K.θS l m ≫ M.q

attribute [reassoc] Lifts.reduces

namespace Lifts

variable {K} (D : K.Lifts)

theorem pointwise [IsArtinianRing R'] (l m : K.L) : IsPointwiseInclusion (D.θ l m) := by
  intro x
  obtain ⟨y, hy⟩ := M.q.surjective ((K.V l ⊓ K.V m).ι x)
  have hy' : y ∈ M.VT (K.V l) ⊓ M.VT (K.V m) := by
    change M.q y ∈ K.V l ⊓ K.V m
    rw [hy]
    exact x.2
  let y' : (M.VT (K.V l) ⊓ M.VT (K.V m)).toScheme := ⟨y, hy'⟩
  have hx : K.res₂ l m y' = x := by
    apply (K.V l ⊓ K.V m).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, M.resTo_ι, Scheme.Hom.comp_apply]
    exact hy
  rw [← hx, ← Scheme.Hom.comp_apply, D.reduces, Scheme.Hom.comp_apply, K.θS_pointwise,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, M.resTo_ι]

theorem fibre (l m : K.L) :
    pullback.fst ((K.V l ⊓ K.V m).ι ≫ M.Y.hom) (specMap (residue R')) ≫ D.θ l m =
      pullback.fst ((K.V l ⊓ K.V m).ι ≫ M.Y.hom) (specMap (residue R')) ≫
        (K.V l ⊓ K.V m).ι := by
  let g := pullback.fst ((K.V l ⊓ K.V m).ι ≫ M.Y.hom) (specMap (residue R'))
  let s := pullback.snd ((K.V l ⊓ K.V m).ι ≫ M.Y.hom) (specMap (residue R'))
  have hgs : g ≫ (K.V l ⊓ K.V m).ι ≫ M.Y.hom = (s ≫ S.c) ≫ S.t := by
    rw [Category.assoc, c_t]
    exact pullback.condition
  have hV : M.VT (K.V l) ⊓ M.VT (K.V m) = M.VT (K.V l ⊓ K.V m) :=
    (Scheme.Hom.preimage_inf _).symm
  let gS := M.liftVT hV g (s ≫ S.c) hgs
  let h := M.isPullback_iE.lift (gS ≫ (M.VT (K.V l) ⊓ M.VT (K.V m)).ι) s (by
    rw [Category.assoc, M.liftVT_pS])
  have hh : gS ≫ (M.VT (K.V l) ⊓ M.VT (K.V m)).ι = h ≫ M.iE :=
    (M.isPullback_iE.lift_fst _ _ _).symm
  have e₁ : g = gS ≫ K.res₂ l m := (M.liftVT_res hV g (s ≫ S.c) hgs).symm
  change g ≫ D.θ l m = g ≫ (K.V l ⊓ K.V m).ι
  rw [e₁, Category.assoc, D.reduces, ← Category.assoc, K.θS_fibre l m gS h hh, Category.assoc,
    Category.assoc, M.resTo_ι]

variable [IsArtinianRing R']

/-- The family of lifted transition maps. -/
abbrev family : Family M.Y where
  L := K.L
  V := K.V
  affine := K.affine
  θ := D.θ
  pointwise := D.pointwise
  overBase := D.overBase
  fibre := D.fibre

theorem res_lift₃ (l m n : K.L) :
    K.res₃ l m n ≫ D.family.lift₃ l m n =
      restrictTo (K.θS m n) (K.θS_pointwise m n)
          (W := M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n))
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ K.res₂ l m := by
  rw [← cancel_mono (K.V l ⊓ K.V m).ι, Category.assoc, Family.lift₃_ι, Category.assoc,
    M.resTo_ι, restrictTo_ι_assoc]
  rw [M.resTo_homOfLE_assoc _ _ (Scheme.Hom.preimage_inf _).symm
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)]
  exact congrArg (M.YS.homOfLE _ ≫ ·) (D.reduces m n)

theorem res_comp (l m n : K.L) :
    K.res₃ l m n ≫ D.family.comp l m n =
      (restrictTo (K.θS m n) (K.θS_pointwise m n)
          (W := M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n))
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ K.θS l m) ≫
        M.q := by
  rw [Family.comp, ← Category.assoc, D.res_lift₃, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (D.reduces l m)

theorem res_direct (l m n : K.L) :
    K.res₃ l m n ≫ D.family.direct l m n =
      (M.YS.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          M.VT (K.V l) ⊓ M.VT (K.V m) ⊓ M.VT (K.V n) ≤ M.VT (K.V l) ⊓ M.VT (K.V n)) ≫
        K.θS l n) ≫ M.q := by
  rw [Family.direct, M.resTo_homOfLE_assoc _ _ (Scheme.Hom.preimage_inf _).symm
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right), Category.assoc]
  exact congrArg (M.YS.homOfLE _ ≫ ·) (D.reduces l n)

/-- The lifted transition maps satisfy the cocycle condition modulo the kernel. -/
theorem agrees [IsSeparated M.Y.hom] : D.family.Agrees (RingHom.ker S.φ) := fun l m n ↦
  M.agreeMod_of_resTo (D.family.affine₃ l m n) _ (by
    rw [D.res_comp, D.res_direct, K.θS_cocycle])

end Lifts

section Existence

variable [IsArtinianRing R'] [IsSeparated M.Y.hom] [Smooth M.Y.hom]

theorem exists_lift₂ (l m : K.L) : ∃ θ : (K.V l ⊓ K.V m).toScheme ⟶ M.Y.left,
    θ ≫ M.Y.hom = (K.V l ⊓ K.V m).ι ≫ M.Y.hom ∧ K.res₂ l m ≫ θ = K.θS l m ≫ M.q := by
  let := S.φ.toAlgebra
  have hU : IsAffineOpen (K.V l ⊓ K.V m) :=
    Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech.affine_inf (K.affine l)
      (K.affine m)
  have : IsAffine (K.V l ⊓ K.V m).toScheme := hU
  exact Langlands.AlgebraicGeometry.AffineNilpotentThickening.exists_lift (R₀ := R) S.surj
    S.nilpotent_ker_φ ((K.V l ⊓ K.V m).ι ≫ M.Y.hom) (K.res₂ l m)
    ((M.VT (K.V l) ⊓ M.VT (K.V m)).ι ≫ M.pS) (M.isPullback_resTo _ _ _) M.Y.hom
    (K.θS l m ≫ M.q) (by
      rw [Category.assoc, M.isPullback_q.w, ← Category.assoc, K.θS_base, M.resTo_over,
        Category.assoc])

/-- The transition maps of the charts have lifts to the model which are the inclusions on the
diagonal. -/
theorem exists_lifts : ∃ D : K.Lifts, ∀ l, D.θ l l = (K.V l ⊓ K.V l).ι := by
  classical
  choose θ h₁ h₂ using K.exists_lift₂
  refine ⟨⟨fun l m ↦ if l = m then (K.V l ⊓ K.V m).ι else θ l m, fun l m ↦ ?_, fun l m ↦ ?_⟩,
    fun l ↦ by simp⟩
  · split_ifs
    · rfl
    · exact h₁ l m
  · split_ifs with h
    · subst h
      rw [K.θS_self, M.resTo_ι]
    · exact h₂ l m

end Existence

end ChartFamily

end Lifts

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
