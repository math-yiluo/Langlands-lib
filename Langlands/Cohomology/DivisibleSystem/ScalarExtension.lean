import Langlands.Cohomology.DivisibleSystem.InverseLimit
import Langlands.Representation.Category.SmoothPartAdjunction
import Langlands.Shimura.Coefficients.Lattice
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Extension of scalars of representations and of Harris's inverse-limit complex

Extension of scalars `V ↦ S ⊗[R] V` and restriction of scalars along an algebra `R → S` for
Mathlib representations, the adjunction between them, their degreewise application to
complexes, and the degreewise smooth part of a complex of representations. Applied to
`quotientInvariantsInverseLimit`, this gives our rendering of Harris's step "Tensoring with
`ℚ_ℓ`" (Harris 1997, p.92; compare `lim 𝓛̃_m ⊗_𝒪 L_ℓ` in Harris 1999, p.311), for a general
algebra `R → S` and for the actual coefficient rings `CoefficientIntegers l → FiniteCompletion L l`.
See `ScalarExtension.md`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits TensorProduct

universe w uR uS uG

section Generic

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {G : Type uG} [Monoid G]

/-- Base change of a representation: `g` acts on `S ⊗[R] V` by `1 ⊗ ρ g`. -/
def baseChangeRepresentation {V : Type w} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) : Representation S G (S ⊗[R] V) where
  toFun g := (ρ g).baseChange S
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' g h := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
theorem baseChangeRepresentation_apply_tmul {V : Type w} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (g : G) (s : S) (v : V) :
    baseChangeRepresentation S ρ g (s ⊗ₜ v) = s ⊗ₜ ρ g v := rfl

variable (R)

/-- An `S`-linear map, viewed as an `R`-linear map between the restrictions of scalars. -/
def restrictScalarsLinearMap {W W' : Type w} [AddCommGroup W] [Module S W] [AddCommGroup W']
    [Module S W'] (f : W →ₗ[S] W') : RestrictScalars R S W →ₗ[R] RestrictScalars R S W' where
  toFun x := (RestrictScalars.addEquiv R S W').symm (f (RestrictScalars.addEquiv R S W x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    simp only [RestrictScalars.addEquiv_map_smul, map_smul, RingHom.id_apply,
      RestrictScalars.addEquiv_symm_map_algebraMap_smul]

@[simp]
theorem restrictScalarsLinearMap_apply {W W' : Type w} [AddCommGroup W] [Module S W]
    [AddCommGroup W'] [Module S W'] (f : W →ₗ[S] W') (x : RestrictScalars R S W) :
    restrictScalarsLinearMap R S f x =
      (RestrictScalars.addEquiv R S W').symm (f (RestrictScalars.addEquiv R S W x)) := rfl

/-- `RestrictScalars.module`, with the additive monoid structure on `RestrictScalars R S M` taken
from its additive group structure, as `Rep.of` requires. Instance search does not identify the
two additive monoid structures, since `RestrictScalars` is not reducible. -/
abbrev restrictScalarsModule (M : Type w) [AddCommGroup M] [Module S M] :
    @Module R (RestrictScalars R S M) _ AddCommGroup.toAddCommMonoid :=
  RestrictScalars.module R S M

attribute [local instance] restrictScalarsModule

/-- Restriction of scalars of a representation along `algebraMap R S`: `g` acts on
`RestrictScalars R S W` by `σ g`. -/
def restrictScalarsRepresentation {W : Type w} [AddCommGroup W] [Module S W]
    (σ : Representation S G W) : Representation R G (RestrictScalars R S W) where
  toFun g := restrictScalarsLinearMap R S (σ g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

/-- The `R`-linear map `v ↦ 1 ⊗ v` into the restriction of scalars of `S ⊗[R] V`. -/
def baseChangeUnitLinearMap (V : Type w) [AddCommGroup V] [Module R V] :
    V →ₗ[R] RestrictScalars R S (S ⊗[R] V) where
  toFun v := (RestrictScalars.addEquiv R S (S ⊗[R] V)).symm (1 ⊗ₜ v)
  map_add' x y := by simp only [tmul_add, map_add]
  map_smul' r v := by
    rw [tmul_smul, RingHom.id_apply, ← algebraMap_smul S r ((1 : S) ⊗ₜ[R] v),
      RestrictScalars.addEquiv_symm_map_algebraMap_smul]

/-- The `S`-linear map `s ⊗ w ↦ s • w` from `S ⊗[R] W`, with `W` viewed as an `R`-module by
restriction of scalars. -/
def baseChangeCounitLinearMap (W : Type w) [AddCommGroup W] [Module S W] :
    S ⊗[R] RestrictScalars R S W →ₗ[S] W :=
  letI := RestrictScalars.moduleOrig R S W
  let l : S ⊗[R] RestrictScalars R S W →ₗ[S] RestrictScalars R S W :=
    LinearMap.liftBaseChange S LinearMap.id
  l

theorem baseChangeCounitLinearMap_tmul (W : Type w) [AddCommGroup W] [Module S W] (s : S)
    (x : RestrictScalars R S W) :
    baseChangeCounitLinearMap R S W (s ⊗ₜ x) = s • RestrictScalars.addEquiv R S W x := rfl

variable (G)

/-- Extension of scalars of representations, `V ↦ S ⊗[R] V`. -/
def repExtendScalars : Rep.{w} R G ⥤ Rep.{max uS w} S G where
  obj V := Rep.of (baseChangeRepresentation S V.ρ)
  map {V W} f := Rep.ofHom ⟨f.hom.toLinearMap.baseChange S, fun g => by
    change f.hom.toLinearMap.baseChange S ∘ₗ (V.ρ g).baseChange S =
      (W.ρ g).baseChange S ∘ₗ f.hom.toLinearMap.baseChange S
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, f.hom.isIntertwining' g]⟩
  map_id V := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_comp _ _

@[simp]
theorem repExtendScalars_map_tmul {V W : Rep.{w} R G} (f : V ⟶ W) (s : S) (v : V) :
    ((repExtendScalars R S G).map f).hom (s ⊗ₜ v) = s ⊗ₜ f.hom v := rfl

/-- Restriction of scalars of representations along `algebraMap R S`. -/
def repRestrictScalars : Rep.{w} S G ⥤ Rep.{w} R G where
  obj W := Rep.of (restrictScalarsRepresentation R S W.ρ)
  map {W W'} f := Rep.ofHom ⟨restrictScalarsLinearMap R S f.hom.toLinearMap, fun g =>
    LinearMap.ext fun x =>
      congrArg (RestrictScalars.addEquiv R S W'.V).symm
        (Rep.hom_comm_apply f g (RestrictScalars.addEquiv R S W.V x))⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance repExtendScalars_additive : (repExtendScalars.{w} R S G).Additive where
  map_add {V W f g} := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_add _ _

instance repRestrictScalars_additive : (repRestrictScalars.{w} R S G).Additive where
  map_add := rfl

/-- The unit of extension and restriction of scalars: `v ↦ 1 ⊗ v`. -/
def repExtendScalarsUnit :
    𝟭 (Rep.{max uS w} R G) ⟶ repExtendScalars R S G ⋙ repRestrictScalars R S G where
  app V := Rep.ofHom ⟨baseChangeUnitLinearMap R S V, fun _ => rfl⟩
  naturality _ _ _ := rfl

@[simp]
theorem repExtendScalarsUnit_app_apply (V : Rep.{max uS w} R G) (v : V) :
    ((repExtendScalarsUnit.{w} R S G).app V).hom v =
      (RestrictScalars.addEquiv R S (S ⊗[R] V)).symm (1 ⊗ₜ v) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The counit of extension and restriction of scalars: `s ⊗ w ↦ s • w`. -/
def repExtendScalarsCounit :
    repRestrictScalars R S G ⋙ repExtendScalars R S G ⟶ 𝟭 (Rep.{max uS w} S G) where
  app W := Rep.ofHom ⟨baseChangeCounitLinearMap R S W, fun g => by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.inductionOn with
    | tmul s x =>
      change s • W.ρ g (RestrictScalars.addEquiv R S W x) =
        W.ρ g (s • RestrictScalars.addEquiv R S W x)
      rw [map_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]⟩
  naturality W W' f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.inductionOn with
    | tmul s x =>
      change s • f.hom (RestrictScalars.addEquiv R S W x) =
        f.hom (s • RestrictScalars.addEquiv R S W x)
      rw [map_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp]
theorem repExtendScalarsCounit_app_tmul (W : Rep.{max uS w} S G) (s : S)
    (x : RestrictScalars R S W) :
    ((repExtendScalarsCounit.{w} R S G).app W).hom (s ⊗ₜ x) =
      s • RestrictScalars.addEquiv R S W x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars is left adjoint to restriction of scalars. -/
def repExtendScalarsAdjunction :
    repExtendScalars.{max uS w} R S G ⊣ repRestrictScalars R S G :=
  Adjunction.mkOfUnitCounit
    { unit := repExtendScalarsUnit R S G
      counit := repExtendScalarsCounit R S G
      left_triangle := by
        refine NatTrans.ext (funext fun V => ?_)
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        refine LinearMap.ext fun t => ?_
        induction t using TensorProduct.inductionOn with
        | tmul s v =>
          change s • ((1 : S) ⊗ₜ[R] v) = s ⊗ₜ[R] v
          rw [smul_tmul', smul_eq_mul, mul_one]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      right_triangle := by
        refine NatTrans.ext (funext fun W => ?_)
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        refine LinearMap.ext fun x => ?_
        change (RestrictScalars.addEquiv R S W).symm
          ((1 : S) • RestrictScalars.addEquiv R S W x) = x
        rw [one_smul]
        rfl }

variable {ι : Type*} (c : ComplexShape ι)

/-- Extension of scalars applied degreewise to complexes of representations. -/
abbrev repExtendScalarsComplex :
    HomologicalComplex (Rep.{w} R G) c ⥤ HomologicalComplex (Rep.{max uS w} S G) c :=
  (repExtendScalars R S G).mapHomologicalComplex c

/-- Restriction of scalars applied degreewise to complexes of representations. -/
abbrev repRestrictScalarsComplex :
    HomologicalComplex (Rep.{w} S G) c ⥤ HomologicalComplex (Rep.{w} R G) c :=
  (repRestrictScalars R S G).mapHomologicalComplex c

/-- The degreewise unit `v ↦ 1 ⊗ v`, a natural chain map from a complex to the restriction of
scalars of its extension of scalars. -/
def repExtendScalarsComplexUnit :
    𝟭 (HomologicalComplex (Rep.{max uS w} R G) c) ⟶
      repExtendScalarsComplex R S G c ⋙ repRestrictScalarsComplex R S G c where
  app K :=
    { f i := (repExtendScalarsUnit R S G).app (K.X i)
      comm' i j _ := ((repExtendScalarsUnit R S G).naturality (K.d i j)).symm }
  naturality _ _ φ :=
    HomologicalComplex.hom_ext _ _ fun i => (repExtendScalarsUnit R S G).naturality (φ.f i)

end Generic

section Smooth

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

instance smoothPartFunctor_additive :
    (SmoothRep.smoothPartFunctor.{uR, uG, w} R G).Additive where
  map_add := rfl

variable {ι : Type*} (c : ComplexShape ι)

/-- The smooth part applied degreewise to a complex of representations. -/
abbrev smoothPartComplex :
    HomologicalComplex (Rep.{w} R G) c ⥤
      HomologicalComplex (SmoothRep.{uR, uG, w} R G) c :=
  (SmoothRep.smoothPartFunctor R G).mapHomologicalComplex c

/-- The degreewise inclusion of smooth vectors, a natural chain map from the smooth part of a
complex to the complex. -/
def smoothPartComplexInclusion :
    smoothPartComplex.{w} R G c ⋙ (SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex c ⟶
      𝟭 (HomologicalComplex (Rep.{w} R G) c) where
  app K :=
    { f i := (SmoothRep.toRepSmoothPartAdjunction R G).counit.app (K.X i)
      comm' i j _ := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality (K.d i j) }
  naturality _ _ φ :=
    HomologicalComplex.hom_ext _ _ fun i =>
      (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality (φ.f i)

end Smooth

namespace DivisibleSystem

section Harris

variable {R : Type uR} [CommRing R] (S : Type uR) [CommRing S] [Algebra R S] {G : Type uG}
  [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map ((K.projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Our rendering of Harris's step "Tensoring with `ℚ_ℓ`": the extension of scalars
`S ⊗[R] -`, degreewise, of `quotientInvariantsInverseLimit`. -/
abbrev quotientInvariantsInverseLimitBaseChange : CochainComplex (Rep.{max w uR uG} S G) ℤ :=
  (repExtendScalarsComplex.{max w uR uG} R S G (ComplexShape.up ℤ)).obj
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk)

/-- The degreewise map `v ↦ 1 ⊗ v` from `quotientInvariantsInverseLimit` to the restriction of
scalars of `quotientInvariantsInverseLimitBaseChange`. -/
abbrev quotientInvariantsInverseLimitToBaseChange :
    quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk ⟶
      (repRestrictScalarsComplex.{max w uR uG} R S G (ComplexShape.up ℤ)).obj
        (quotientInvariantsInverseLimitBaseChange.{w, uR, uG} S N K H hH hK hk) :=
  (repExtendScalarsComplexUnit.{max w uR uG} R S G (ComplexShape.up ℤ)).app
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk)

variable [IsTopologicalGroup G]

/-- The degreewise smooth part of `quotientInvariantsInverseLimitBaseChange`, a complex of
smooth representations. -/
abbrev quotientInvariantsInverseLimitBaseChangeSmooth :
    CochainComplex (SmoothRep.{uR, uG, max w uR uG} S G) ℤ :=
  (smoothPartComplex.{max w uR uG} S G (ComplexShape.up ℤ)).obj
    (quotientInvariantsInverseLimitBaseChange.{w, uR, uG} S N K H hH hK hk)

/-- The degreewise inclusion of `quotientInvariantsInverseLimitBaseChangeSmooth` into
`quotientInvariantsInverseLimitBaseChange`. -/
abbrev quotientInvariantsInverseLimitBaseChangeSmoothInclusion :
    ((SmoothRep.toRep (R := S) (G := G)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (quotientInvariantsInverseLimitBaseChangeSmooth.{w, uR, uG} S N K H hH hK hk) ⟶
      quotientInvariantsInverseLimitBaseChange.{w, uR, uG} S N K H hH hK hk :=
  (smoothPartComplexInclusion.{max w uR uG} S G (ComplexShape.up ℤ)).app
    (quotientInvariantsInverseLimitBaseChange.{w, uR, uG} S N K H hH hK hk)

end Harris

section Coefficients

open Langlands.Global Langlands.Shimura.Coefficients

variable {L : Type uR} [Field L] [NumberField L] (l : FinitePlace L) {G : Type uG} [Group G]
  [TopologicalSpace G] {ℓ : ℕ} (N : ℕ)
  (K : DivisibleSystem
    (CochainComplex (SmoothRep.{uR, uG, max w uR uG} (CoefficientIntegers l) G) ℕ) ℓ)
  {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants (CoefficientIntegers l) (H i)).map ((K.projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j),
    IsUnit (Nat.card (quotientProjection (hH hij)).ker : CoefficientIntegers l))
  [IsFiltered ι]

/-- `quotientInvariantsInverseLimitBaseChange` for coefficients in the actual local ring of
integers `CoefficientIntegers l` at a finite place `l` of a number field `L`, extended to the
completion `FiniteCompletion L l`. -/
abbrev quotientInvariantsInverseLimitCompletion :
    CochainComplex (Rep.{max w uR uG} (FiniteCompletion L l) G) ℤ :=
  quotientInvariantsInverseLimitBaseChange.{w, uR, uG} (FiniteCompletion L l) N K H hH hK hk

/-- `quotientInvariantsInverseLimitToBaseChange` for `CoefficientIntegers l` and
`FiniteCompletion L l`. -/
abbrev quotientInvariantsInverseLimitToCompletion :
    quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk ⟶
      (repRestrictScalarsComplex.{max w uR uG} (CoefficientIntegers l) (FiniteCompletion L l) G
        (ComplexShape.up ℤ)).obj
        (quotientInvariantsInverseLimitCompletion.{w, uR, uG} l N K H hH hK hk) :=
  quotientInvariantsInverseLimitToBaseChange.{w, uR, uG} (FiniteCompletion L l) N K H hH hK hk

variable [IsTopologicalGroup G]

/-- `quotientInvariantsInverseLimitBaseChangeSmooth` for `CoefficientIntegers l` and
`FiniteCompletion L l`. -/
abbrev quotientInvariantsInverseLimitCompletionSmooth :
    CochainComplex (SmoothRep.{uR, uG, max w uR uG} (FiniteCompletion L l) G) ℤ :=
  quotientInvariantsInverseLimitBaseChangeSmooth.{w, uR, uG} (FiniteCompletion L l) N K H hH hK
    hk

/-- `quotientInvariantsInverseLimitBaseChangeSmoothInclusion` for `CoefficientIntegers l` and
`FiniteCompletion L l`. -/
abbrev quotientInvariantsInverseLimitCompletionSmoothInclusion :
    ((SmoothRep.toRep (R := FiniteCompletion L l) (G := G)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (quotientInvariantsInverseLimitCompletionSmooth.{w, uR, uG} l N K H hH hK hk) ⟶
      quotientInvariantsInverseLimitCompletion.{w, uR, uG} l N K H hH hK hk :=
  quotientInvariantsInverseLimitBaseChangeSmoothInclusion.{w, uR, uG} (FiniteCompletion L l) N K
    H hH hK hk

end Coefficients

end DivisibleSystem

end Langlands.Cohomology
