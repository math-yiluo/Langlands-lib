import Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclic
import Langlands.Sheaf.Equivariant.TwistedInductionFixedCoordinates

/-! # Smooth point products have coinduced Galois fixed sections -/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

universe u v uL z w

section Coinduction

variable {Γ : Type*} [Group Γ]

/-- For a free action, every element is uniquely a translate of the chosen representative of
its orbit. -/
theorem orbitMap_bijective {T Q : Type*} [MulAction Γ T]
    (hfree : ∀ (γ : Γ) (t : T), γ • t = t → γ = 1)
    (e : Q ≃ Quotient (MulAction.orbitRel Γ T)) :
    Function.Bijective fun p : Γ × Q => p.1 • (e p.2).out := by
  constructor
  · rintro ⟨γ, o⟩ ⟨γ', o'⟩ hp
    change γ • (e o).out = γ' • (e o').out at hp
    have ho : e o = e o' := by
      rw [← Quotient.out_eq (e o), ← Quotient.out_eq (e o')]
      apply Quotient.sound
      change MulAction.orbitRel Γ T (e o).out (e o').out
      rw [MulAction.orbitRel_apply]
      refine ⟨γ⁻¹ * γ', ?_⟩
      change (γ⁻¹ * γ') • (e o').out = (e o).out
      rw [mul_smul, ← hp, inv_smul_smul]
    obtain rfl := e.injective ho
    have hγ : (γ'⁻¹ * γ) • (e o).out = (e o).out := by
      rw [mul_smul, hp, inv_smul_smul]
    have h1 := hfree _ _ hγ
    rw [inv_mul_eq_one] at h1
    rw [h1]
  · intro t
    have ht := Quotient.mk_out (s := MulAction.orbitRel Γ T) t
    rw [MulAction.orbitRel_apply] at ht
    obtain ⟨γ, hγ⟩ := ht
    refine ⟨(γ⁻¹, e.symm ⟦t⟧), ?_⟩
    change γ⁻¹ • (e (e.symm ⟦t⟧)).out = t
    rw [e.apply_symm_apply]
    rw [← hγ, inv_smul_smul]

/-- **Coinduction for free actions.** Functions on a free `Γ`-set are functions on `Γ` with
values in functions on the orbits: `u ↦ (γ ↦ (o ↦ u (γ • rep o)))` is bijective. -/
theorem coinduced_bijective {T Q N : Type*} [MulAction Γ T]
    (hfree : ∀ (γ : Γ) (t : T), γ • t = t → γ = 1)
    (e : Q ≃ Quotient (MulAction.orbitRel Γ T)) :
    Function.Bijective fun (u : T → N) (γ : Γ) (o : Q) => u (γ • (e o).out) := by
  have hf := orbitMap_bijective hfree e
  let f := Equiv.ofBijective _ hf
  constructor
  · intro u u' huu
    funext t
    obtain ⟨⟨γ, o⟩, rfl⟩ := hf.2 t
    exact congrFun (congrFun huu γ) o
  · intro w
    refine ⟨fun t => w (f.symm t).1 (f.symm t).2, ?_⟩
    funext γ o
    have hs : f.symm (γ • (e o).out) = (γ, o) := f.symm_apply_apply (γ, o)
    change w (f.symm (γ • (e o).out)).1 (f.symm (γ • (e o).out)).2 = w γ o
    rw [hs]

/-- Coinduction for a family of free `Γ`-sets, with coefficients depending on the family
index. -/
theorem coinduced_pi_bijective {ι : Type*} {T Q N : ι → Type*} [∀ i, MulAction Γ (T i)]
    (hfree : ∀ i (γ : Γ) (t : T i), γ • t = t → γ = 1)
    (e : ∀ i, Q i ≃ Quotient (MulAction.orbitRel Γ (T i))) :
    Function.Bijective fun (u : ∀ i, T i → N i) (γ : Γ) (i : ι) (o : Q i) =>
      u i (γ • (e i o).out) := by
  have hb := fun i => coinduced_bijective (N := N i) (hfree i) (e i)
  constructor
  · intro u u' huu
    funext i
    apply (hb i).1
    funext γ o
    exact congrFun (congrFun (congrFun huu γ) i) o
  · intro w
    choose u hu using fun i => (hb i).2 fun γ o => w γ i o
    refine ⟨u, ?_⟩
    funext γ i o
    exact congrFun (congrFun (hu i) γ) o

end Coinduction

section DeckNaturality

variable {C : Type*} [Category C] {P : MorphismProperty C} [P.RespectsIso]
variable {Y : C} {G : Type*} [Group G] (ρ : G →* Aut Y)
variable {R : Type w} [CommRing R]

/-- A twisted arrow reindexes the coordinates of the actual induction, with the target label
prescribed by `transportTo`. -/
theorem projection_map_transportTo
    [∀ F : (P.Over ⊤ Y)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
    (F : (P.Over ⊤ Y)ᵒᵖ ⥤ ModuleCat.{w} R) {U V : TwistedOver P ρ} (f : U ⟶ V)
    (g g' : G) (hg : g' = g * (Hom.twist f)⁻¹) (s : ((ι P ρ).op.ran.obj F).obj (op V)) :
    projection ρ F U g (((ι P ρ).op.ran.obj F).map f.op s) =
      F.map (transportTo ρ f g g' hg).op (projection ρ F V g' s) := by
  subst hg
  exact congrArg (fun k => k.hom s) (map_projection ρ F f g)

end DeckNaturality

section Analytic

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable (G : Type z) [Group G] (ρ : G →* Aut X)

variable {X G ρ} in
theorem twist_deckEndomorphism (V : TwistedOver (etale (K := K)) ρ)
    (e : V.obj.left ≅ V.obj.left) (he : e.hom ≫ V.hom = V.hom) :
    Hom.twist (deckEndomorphism V e he) = 1 :=
  rfl

variable {X G ρ} in
/-- The ordinary arrow underlying a deck transformation between translates of `V` by the
same element. -/
def deckTransport (V : TwistedOver (etale (K := K)) ρ) (e : V.obj.left ≅ V.obj.left)
    (he : e.hom ≫ V.hom = V.hom) (g : G) :
    (TwistedOver.translate etale ρ g).obj V.obj ⟶ (TwistedOver.translate etale ρ g).obj V.obj :=
  transportTo ρ (deckEndomorphism V e he) g g (by rw [twist_deckEndomorphism, inv_one, mul_one])

variable {X G ρ} in
@[simp]
theorem deckTransport_left (V : TwistedOver (etale (K := K)) ρ) (e : V.obj.left ≅ V.obj.left)
    (he : e.hom ≫ V.hom = V.hom) (g : G) :
    (deckTransport V e he g).left = e.hom :=
  rfl

section Fibers

variable {X G ρ}
variable {Γ : Type} [Group Γ] (V : TwistedOver (etale (K := K)) ρ)
variable (deck : Γ →* Aut V.obj.left) (hdeck : ∀ γ : Γ, (deck γ).asIso.hom ≫ V.hom = V.hom)
variable (Kₒ : Subgroup G) (i : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X))

/-- The coordinates of index `i` over `V`: a left coset of `Kₒ` together with a point of the
`i`-th fibre of the translate of `V` by the chosen coset representative. -/
abbrev CosetFiber : Type (max z (max u (v + 1) uL)) :=
  Σ c : G ⧸ Kₒ, (etaleGodementPoints.{u, v, uL} L h i).fiber.obj
    ((TwistedOver.translate etale ρ c.out).obj V.obj)

/-- Deck transformations act on the coordinates of index `i` through the fibres. -/
abbrev cosetFiberAction : MulAction Γ (CosetFiber L h V Kₒ i) where
  smul γ t := ⟨t.1, (etaleGodementPoints.{u, v, uL} L h i).fiber.map
    (deckTransport V (deck γ).asIso (hdeck γ) t.1.out) t.2⟩
  one_smul t := by
    obtain ⟨c, p⟩ := t
    refine congrArg (Sigma.mk c) ?_
    have e : deckTransport V (deck 1).asIso (hdeck 1) c.out = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      change (deck 1).asIso.hom = 𝟙 _
      rw [map_one]
      rfl
    rw [e, Functor.map_id_apply]
  mul_smul γ δ t := by
    obtain ⟨c, p⟩ := t
    refine congrArg (Sigma.mk c) ?_
    have e : deckTransport V (deck (γ * δ)).asIso (hdeck (γ * δ)) c.out =
        deckTransport V (deck δ).asIso (hdeck δ) c.out ≫ deckTransport V (deck γ).asIso (hdeck γ) c.out := by
      apply MorphismProperty.Over.Hom.ext
      change (deck (γ * δ)).asIso.hom = (deck δ).asIso.hom ≫ (deck γ).asIso.hom
      rw [map_mul]
      rfl
    change (etaleGodementPoints.{u, v, uL} L h i).fiber.map _ p = _
    rw [e, Functor.map_comp_apply]
    rfl

end Fibers

section Main

variable [∀ F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R,
  (ι (etale (K := K)) ρ).op.HasPointwiseRightKanExtension F]

variable {X R G ρ} in
/-- Restriction along a deck transformation, in the point coordinates of the translate by
`g`: the coordinate at `p` becomes the coordinate at the image of `p`. -/
theorem sectionCoordinates_projection_deck
    (M : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X) →
      ModuleCat.{max u (v + 1) uL} R)
    (V : TwistedOver (etale (K := K)) ρ) (e : V.obj.left ≅ V.obj.left)
    (he : e.hom ≫ V.hom = V.hom) (g : G)
    (t : ((ι etale ρ).op.ran.obj (Langlands.Sheaf.PointProduct.productSheaf (etaleGodementPoints.{u, v, uL} L h)
      (ModuleCat.{max u (v + 1) uL} R) M).obj).obj (op V))
    (i : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X))
    (p : (etaleGodementPoints.{u, v, uL} L h i).fiber.obj
      ((TwistedOver.translate etale ρ g).obj V.obj)) :
    Langlands.Sheaf.PointProduct.sectionCoordinates.{max u (v + 1) uL, max u (v + 1) uL}
        (etaleGodementPoints.{u, v, uL} L h) M ((TwistedOver.translate etale ρ g).obj V.obj)
        (projection ρ (Langlands.Sheaf.PointProduct.productSheaf (etaleGodementPoints.{u, v, uL} L h)
          (ModuleCat.{max u (v + 1) uL} R) M).obj V g
          (((ι etale ρ).op.ran.obj (Langlands.Sheaf.PointProduct.productSheaf (etaleGodementPoints.{u, v, uL} L h)
          (ModuleCat.{max u (v + 1) uL} R) M).obj).map
            (deckEndomorphism V e he).op t)) i p =
      Langlands.Sheaf.PointProduct.sectionCoordinates.{max u (v + 1) uL, max u (v + 1) uL}
        (etaleGodementPoints.{u, v, uL} L h) M ((TwistedOver.translate etale ρ g).obj V.obj)
        (projection ρ (Langlands.Sheaf.PointProduct.productSheaf (etaleGodementPoints.{u, v, uL} L h)
          (ModuleCat.{max u (v + 1) uL} R) M).obj V g t) i
        ((etaleGodementPoints.{u, v, uL} L h i).fiber.map (deckTransport V e he g) p) := by
  rw [projection_map_transportTo ρ _ (deckEndomorphism V e he) g g
    (by rw [twist_deckEndomorphism, inv_one, mul_one]) t]
  exact Langlands.Sheaf.PointProduct.sectionCoordinates_restrict.{max u (v + 1) uL, max u (v + 1) uL} _ _ _ _ _

/-- Reindexing a family of coefficient functions by a sigma type is bijective. -/
theorem sigmaReindex_bijective {α ι : Type*} {β : α → ι → Type*} {N : ι → Type*} :
    Function.Bijective fun (u : ∀ a i, β a i → N i) (i : ι) (t : Σ a, β a i) => u t.1 i t.2 := by
  constructor
  · intro u u' huu
    funext a i b
    exact congrFun (congrFun huu i) ⟨a, b⟩
  · intro w
    exact ⟨fun a i b => w i ⟨a, b⟩, rfl⟩

variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- **The actual smooth point products have coinduced Galois fixed sections.** Over an
equivariant finite Galois datum, the `Kₒ`-fixed sections are coefficient families on the
coset fibres, on which the deck group acts freely; evaluating at chosen orbit
representatives exhibits them as a coinduced module. -/
theorem hasCoinducedGaloisFixedSections_smoothPointProduct
    (M : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X) →
      ModuleCat.{max u (v + 1) uL} R) :
    HasCoinducedGaloisFixedSections L
      ((smoothPointProductFunctor ρ (etaleTopology X) (distinguishedLiftSystem ρ)
        (etaleGodementPoints.{u, v, uL} L h) R).obj M) := by
  intro V hV Γ _ _ deck hdeck hfree l _ Kₒ hKₒ hK
  let points := etaleGodementPoints.{u, v, uL} L h
  let F₀ := (Langlands.Sheaf.PointProduct.productSheaf points (ModuleCat.{max u (v + 1) uL} R) M).obj
  let raw := (ι etale ρ).op.ran.obj F₀
  let S := (smoothPointProductFunctor ρ (etaleTopology X) (distinguishedLiftSystem ρ)
    points R).obj M
  let act : ∀ i, MulAction Γ (CosetFiber L h V Kₒ i) :=
    fun i => cosetFiberAction L h V deck hdeck Kₒ i
  let Q := fun i => Quotient (MulAction.orbitRel Γ (CosetFiber L h V Kₒ i))
  have : Small.{max u (v + 1) uL} (G ⧸ Kₒ) := small_of_surjective QuotientGroup.mk_surjective
  have : ∀ i, Small.{max u (v + 1) uL} (Q i) := fun i =>
    small_of_surjective (Quotient.mk_surjective (s := MulAction.orbitRel Γ _))
  let e : ∀ i, Shrink.{max u (v + 1) uL} (Q i) ≃ Q i := fun i => (equivShrink (Q i)).symm
  let rep : ∀ i, Shrink.{max u (v + 1) uL} (Q i) → CosetFiber L h V Kₒ i :=
    fun i o => (e i o).out
  let coord : ∀ (g : G) (i)
      (_ : (points i).fiber.obj ((TwistedOver.translate etale ρ g).obj V.obj)),
      raw.obj (op V) →ₗ[R] M i := fun g i p =>
    LinearMap.proj p ∘ₗ LinearMap.proj i ∘ₗ
      (Langlands.Sheaf.PointProduct.sectionCoordinates.{max u (v + 1) uL, max u (v + 1) uL}
        points M _).toLinearMap ∘ₗ (projection ρ F₀ V g).hom
  let A : ModuleCat.{max u (v + 1) uL} R :=
    ModuleCat.of R (∀ i, Shrink.{max u (v + 1) uL} (Q i) → M i)
  let sm := LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ)
    (twistedEtaleTopology ρ) raw V
  let π : sm →ₗ[R] A := LinearMap.pi fun i => LinearMap.pi fun o =>
    coord (rep i o).1.out i (rep i o).2 ∘ₗ sm.subtype
  refine ⟨A, π, ?_⟩
  -- the lift and the fixed coordinates of the raw induction
  have hlift : IsLift (liftAction l) := fun _ => rfl
  let Φ := pointProductFixedCoordinates ρ points M hlift (K := Kₒ) hK
  let val : S.obj.obj.obj (op V) → raw.obj (op V) := fun x => (@id sm x).1
  have hval : Function.Injective val := Subtype.val_injective
  have hmemFix : ∀ x : S.obj.obj.obj (op V),
      x ∈ liftFixedSubmodule S V l Kₒ hK ↔ val x ∈ fixedSubmodule ρ F₀ (liftAction l) Kₒ := by
    intro x
    rw [mem_fixedSubmodule_iff, liftFixedSubmodule]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    constructor
    · intro hfix k hk
      exact congrArg val (hfix k hk)
    · intro hfix k hk
      exact hval (hfix ⟨k, hK hk⟩ hk)
  have hadm : (distinguishedLiftSystem ρ).IsAdmissible V (liftOpenSubgroup l) (liftAction l) :=
    ⟨hV, l, le_rfl, MonoidHom.ext fun _ => rfl⟩
  let f₁ : liftFixedSubmodule S V l Kₒ hK → fixedSubmodule ρ F₀ (liftAction l) Kₒ :=
    fun s => ⟨val s.1, (hmemFix s.1).1 s.2⟩
  have hf₁ : Function.Bijective f₁ := by
    constructor
    · intro s s' hss
      have hv := congrArg Subtype.val hss
      exact Subtype.ext (hval hv)
    · intro t
      have hs : t.1 ∈ sm := fixedSubmodule_le_smoothSubmodule ρ (distinguishedLiftSystem ρ)
        (twistedEtaleTopology ρ) F₀ hadm ⟨Kₒ, hKₒ⟩ hK t.2
      exact ⟨⟨@id (S.obj.obj.obj (op V)) (⟨t.1, hs⟩ : sm), (hmemFix _).2 t.2⟩, rfl⟩
  let C := (fun (u : ∀ i, CosetFiber L h V Kₒ i → M i) (γ : Γ) (i)
      (o : Shrink.{max u (v + 1) uL} (Q i)) => u i (γ • (e i o).out)) ∘
    (fun (u : ∀ (c : G ⧸ Kₒ) i, (points i).fiber.obj
        ((TwistedOver.translate etale ρ c.out).obj V.obj) → M i) i
      (t : CosetFiber L h V Kₒ i) => u t.1 i t.2)
  have hC : Function.Bijective C := by
    refine Function.Bijective.comp ?_ sigmaReindex_bijective
    refine coinduced_pi_bijective (fun i γ t ht => ?_) e
    obtain ⟨c, p⟩ := t
    have hp : (points i).fiber.map (deckTransport V (deck γ).asIso (hdeck γ) c.out) p = p :=
      eq_of_heq (Sigma.mk.inj_iff.1 ht).2
    exact hfree γ p.down.1 (congrArg (fun q => q.down.1) hp)
  have key : (fun s : liftFixedSubmodule S V l Kₒ hK => fun γ : Γ =>
      π ((S.obj.obj.map (deckEndomorphism V (deck γ).asIso (hdeck γ)).op).hom s.1)) =
      C ∘ Φ ∘ f₁ := by
    funext s γ i o
    change Langlands.Sheaf.PointProduct.sectionCoordinates.{max u (v + 1) uL, max u (v + 1) uL}
        points M _ (projection ρ F₀ V (rep i o).1.out
          (raw.map (deckEndomorphism V (deck γ).asIso (hdeck γ)).op (val s.1))) i (rep i o).2 =
      Φ (f₁ s) (rep i o).1 i
        ((points i).fiber.map (deckTransport V (deck γ).asIso (hdeck γ) (rep i o).1.out) (rep i o).2)
    refine (sectionCoordinates_projection_deck L h M V (deck γ).asIso (hdeck γ) _ (val s.1) i _).trans ?_
    rfl
  exact (congrArg Function.Bijective key).mpr (hC.comp (Φ.bijective.comp hf₁))

end Main

section Reduction

variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- **Reduction to the Galois-coinduced input.** The Galois-coinduced local acyclicity
statement implies the local higher-direct-image vanishing for the actual restricted smooth
point products. -/
theorem analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced
    (hC : AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ) :
    AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement L X h R G ρ := by
  intro hT2 _ hcont N _ q
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exact hC hT2 hcont _ (hasCoinducedGaloisFixedSections_smoothPointProduct L X h R G ρ _) q

end Reduction

end Analytic

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
