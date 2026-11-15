import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingFac
import Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Factorization on the spectrum of a local ring (SGA 3, XI 3.1)

Let `ξ ∈ F(U)` be a monomorphism `U → F` that is infinitesimally étale at every point, and
let `η ∈ F(T)`. This module proves that if `η` factors through `ξ` at the residue field of
a point `t` of `T` whose local ring is noetherian, then `η` factors through `ξ` on
`Spec 𝒪_{T,t}`. This is the step (iii) ⇒ (ii) in the proof of SGA 3, XI 3.1: one lifts the
factorization to the artinian quotients of the completion by infinitesimal étaleness, passes
to the completion by condition (F3), and descends along the faithfully flat completion map
by condition (F1b). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing

/-! ### Morphisms out of the spectrum of a complete local ring -/

section Adic

variable {A : Type u} [CommRing A] [IsLocalRing A]

lemma maximalIdeal_pow_succ_ne_top (n : ℕ) : maximalIdeal A ^ (n + 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self n.succ_ne_zero)

instance (n : ℕ) : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal_pow_succ_ne_top n)

instance (n : ℕ) : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Every point of `Spec (A / m^(n+1))` lies over the closed point of `Spec A`. -/
lemma comap_mk_maximalIdeal_pow (n : ℕ) (q : PrimeSpectrum (A ⧸ maximalIdeal A ^ (n + 1))) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) q = closedPoint A := by
  have hq : (Ideal.comap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) q.asIdeal).IsPrime :=
    Ideal.comap_isPrime _ _
  ext1
  refine ((maximalIdeal.isMaximal A).eq_of_le hq.ne_top ?_).symm
  refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun x hx ↦ ?_
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact zero_mem _

/-- `Spec (A / m^(n+1))` has a single point. -/
lemma eq_of_quotient_pow (n : ℕ) (x y : PrimeSpectrum (A ⧸ maximalIdeal A ^ (n + 1))) :
    x = y :=
  PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    ((comap_mk_maximalIdeal_pow n x).trans (comap_mk_maximalIdeal_pow n y).symm)

/-- A local homomorphism of local rings maps the closed point to the closed point. -/
lemma specMap_closedPoint {B C : Type u} [CommRing B] [CommRing C] [IsLocalRing B]
    [IsLocalRing C] (φ : B →+* C) [IsLocalHom φ] :
    Spec.map (CommRingCat.ofHom φ) (closedPoint C) = closedPoint B :=
  IsLocalRing.comap_closedPoint φ

/-- A morphism out of the spectrum of a local ring lands in every open set containing the
image of the closed point. -/
lemma range_subset_of_isLocalRing {B : Type u} [CommRing B] [IsLocalRing B] {X : Scheme.{u}}
    (g : Spec (CommRingCat.of B) ⟶ X) {V : Set X} (hV : IsOpen V)
    (h : g (closedPoint B) ∈ V) : Set.range g ⊆ V := by
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint (R := B) x).map g.continuous).mem_open hV h

lemma strictMono_add_one : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1

variable [IsAdicComplete (maximalIdeal A) A]

/-- A compatible family of morphisms `Spec (A / m^(n+1)) ⟶ X` comes from a morphism
`Spec A ⟶ X`, for `A` a complete local ring. -/
theorem exists_specMap_adic_lift {X : Scheme.{u}}
    (u : ∀ n : ℕ, Spec (CommRingCat.of (A ⧸ maximalIdeal A ^ (n + 1))) ⟶ X)
    (hu : ∀ n : ℕ, Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factorPow (maximalIdeal A) (n + 1).le_succ)) ≫ u (n + 1) = u n) :
    ∃ g : Spec (CommRingCat.of A) ⟶ X, ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))) ≫ g = u n := by
  have hpt : ∀ n, u n (closedPoint _) = u 0 (closedPoint _) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [← ih, ← hu n]
      exact (congrArg (u (n + 1)) (eq_of_quotient_pow _ _ _)).trans
        (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨R, ι, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X) (x := u 0 (closedPoint _)) (U := ⊤) trivial
  have hr : ∀ n, Set.range (u n) ⊆ Set.range ι := fun n ↦
    range_subset_of_isLocalRing (u n) ι.isOpenEmbedding.isOpen_range (by rw [hpt]; exact hx)
  let ψ : ∀ n, R →+* A ⧸ maximalIdeal A ^ (n + 1) := fun n ↦
    (Spec.preimage (IsOpenImmersion.lift ι (u n) (hr n))).hom
  have hψ' : ∀ n, Spec.map (CommRingCat.ofHom (ψ n)) ≫ ι = u n := fun n ↦ by
    simp only [ψ, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hψ : ∀ {m}, (Ideal.Quotient.factorPow (maximalIdeal A)
      (strictMono_add_one.monotone m.le_succ)).comp (ψ (m + 1)) = ψ m := by
    intro m
    have : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.factorPow (maximalIdeal A)
        (strictMono_add_one.monotone m.le_succ)).comp (ψ (m + 1)))) =
        Spec.map (CommRingCat.ofHom (ψ m)) := by
      rw [← cancel_mono ι, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψ', hψ']
      exact hu m
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  refine ⟨Spec.map (CommRingCat.ofHom (IsAdicComplete.StrictMono.liftRingHom (maximalIdeal A)
    strictMono_add_one ψ hψ)) ≫ ι, fun n ↦ ?_⟩
  have key := IsAdicComplete.StrictMono.mk_comp_liftRingHom (maximalIdeal A) strictMono_add_one
    ψ hψ (n := n)
  beta_reduce at key
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.algebraMap_eq,
    key, hψ']

/-- Two morphisms `Spec A ⟶ X` agreeing on every `Spec (A / m^(n+1))` are equal, for `A` a
complete local ring. -/
theorem specMap_adic_ext {X : Scheme.{u}} {g₁ g₂ : Spec (CommRingCat.of A) ⟶ X}
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))) ≫ g₁ =
        Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))) ≫ g₂) :
    g₁ = g₂ := by
  have hc : ∀ g : Spec (CommRingCat.of A) ⟶ X,
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (0 + 1)))) ≫ g)
        (closedPoint _) = g (closedPoint A) := by
    intro g
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg g (comap_mk_maximalIdeal_pow 0 _))
  have h12 : g₂ (closedPoint A) = g₁ (closedPoint A) := by rw [← hc g₁, ← hc g₂, h 0]
  obtain ⟨R, ι, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X) (x := g₁ (closedPoint A)) (U := ⊤) trivial
  have hr₁ := range_subset_of_isLocalRing g₁ ι.isOpenEmbedding.isOpen_range hx
  have hr₂ := range_subset_of_isLocalRing g₂ ι.isOpenEmbedding.isOpen_range (h12 ▸ hx)
  have e₁ : Spec.map (Spec.preimage (IsOpenImmersion.lift ι g₁ hr₁)) ≫ ι = g₁ := by simp
  have e₂ : Spec.map (Spec.preimage (IsOpenImmersion.lift ι g₂ hr₂)) ≫ ι = g₂ := by simp
  suffices Spec.preimage (IsOpenImmersion.lift ι g₁ hr₁) =
      Spec.preimage (IsOpenImmersion.lift ι g₂ hr₂) by
    rw [← e₁, ← e₂, this]
  apply CommRingCat.hom_ext
  apply DFunLike.coe_injective
  refine IsHausdorff.StrictMono.funext' (maximalIdeal A) strictMono_add_one fun n x ↦ ?_
  have : Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))) ≫
      Spec.map (Spec.preimage (IsOpenImmersion.lift ι g₁ hr₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))) ≫
        Spec.map (Spec.preimage (IsOpenImmersion.lift ι g₂ hr₂)) := by
    rw [← cancel_mono ι, Category.assoc, Category.assoc, e₁, e₂]
    exact h n
  rw [← Spec.map_comp, ← Spec.map_comp] at this
  have := congrArg (fun φ ↦ φ.hom x) (Spec.map_injective this)
  simpa [Ideal.Quotient.algebraMap_eq] using this

end Adic

/-! ### Factorization over artinian and complete local rings -/

/-- Restriction along an algebra map followed by the structure map is the structure map. -/
lemma algHomOver_comp_algebraOverBase {S : Scheme.{u}} {B : Type u} [CommRing B]
    (f : Spec (CommRingCat.of B) ⟶ S) {C D : Type u} [CommRing C] [Algebra B C] [CommRing D]
    [Algebra B D] (φ : C →ₐ[B] D) :
    algHomOver f φ ≫ algebraOverBase f C = algebraOverBase f D := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, algHomOver, algebraOverBase, Over.homMk_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {U : Over S} {ξ : F.obj (op U)}

/-- Over a local artinian ring, factorization at the closed point implies factorization, by
infinitesimal étaleness. -/
lemma fac_id_of_isArtinianRing (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    (hét : ∀ y, InfinitesimallyEtaleAt F ξ y) {B : Type u} [CommRing B] [IsLocalRing B]
    [IsArtinianRing B] (f : Spec (CommRingCat.of B) ⟶ S) (η : F.obj (op (Over.mk f)))
    (h0 : closedPoint B ∈ W ξ η) : Fac ξ η (𝟙 _) := by
  have hJ : IsNilpotent (maximalIdeal B) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
  let := Ideal.Quotient.field (maximalIdeal B)
  let g := algebraOverBase f (B ⧸ maximalIdeal B)
  have hg : Fac ξ η g := by
    have : IsLocalHom (algebraMap B (B ⧸ maximalIdeal B)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    refine (fac_fieldPt_iff (K := B ⧸ maximalIdeal B) hmono hF g).mpr ?_
    have hpt : g.left (closedPoint (B ⧸ maximalIdeal B)) = closedPoint B :=
      specMap_closedPoint (algebraMap B (B ⧸ maximalIdeal B))
    exact (Set.mem_of_eq_of_mem hpt h0 :
      g.left (closedPoint (B ⧸ maximalIdeal B)) ∈ W ξ η)
  obtain ⟨u₀, hu₀⟩ := hg
  obtain ⟨u, ⟨-, hu⟩, -⟩ := hét (u₀.left (closedPoint (B ⧸ maximalIdeal B))) B f
    (maximalIdeal B) hJ u₀ (fun x ↦ congrArg u₀.left
      (Subsingleton.elim (α := Spec (CommRingCat.of (B ⧸ maximalIdeal B))) x _)) η hu₀
  refine ⟨u, ?_⟩
  rw [hu, op_id, F.map_id]
  rfl

/-- Factorization at every artinian quotient `A / m^(n+1)` of a noetherian local ring. -/
lemma fac_quotient_pow (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    (hét : ∀ y, InfinitesimallyEtaleAt F ξ y) {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : Spec (CommRingCat.of A) ⟶ S) (η : F.obj (op (Over.mk f)))
    (h0 : closedPoint A ∈ W ξ η) (n : ℕ) :
    Fac ξ η (algebraOverBase f (A ⧸ maximalIdeal A ^ (n + 1))) := by
  have : IsNoetherianRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
    isNoetherianRing_of_surjective A _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hnil : IsNilpotent (maximalIdeal (A ⧸ maximalIdeal A ^ (n + 1))) := ⟨n + 1, by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow]
    exact Ideal.map_mk_eq_bot_of_le le_rfl⟩
  have : IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr hnil
  have : IsLocalHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have key := fac_id_of_isArtinianRing hmono hF hét
    (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))) ≫ f)
    (F.map (algebraOverBase f (A ⧸ maximalIdeal A ^ (n + 1))).op η) (by
      refine (mem_W_map_iff hmono hF _ _ _).mpr ?_
      have hpt : (algebraOverBase f (A ⧸ maximalIdeal A ^ (n + 1))).left
          (closedPoint (A ⧸ maximalIdeal A ^ (n + 1))) = closedPoint A :=
        specMap_closedPoint (algebraMap A (A ⧸ maximalIdeal A ^ (n + 1)))
      exact Set.mem_of_eq_of_mem hpt h0)
  rw [fac_map_iff, Category.id_comp] at key
  exact key

/-- SGA 3, XI 3.1, (iii) ⇒ (ii) over a complete local noetherian ring: factorization at the
closed point implies factorization. -/
theorem fac_id_of_isAdicComplete (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    (hét : ∀ y, InfinitesimallyEtaleAt F ξ y) (hA : AdicLimits F) {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    (f : Spec (CommRingCat.of A) ⟶ S) (η : F.obj (op (Over.mk f)))
    (h0 : closedPoint A ∈ W ξ η) : Fac ξ η (𝟙 _) := by
  choose u hu using fac_quotient_pow hmono hF hét f η h0
  have hcompat : ∀ n, algHomOver f (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (I := maximalIdeal A) (n + 1).le_succ)) ≫ u (n + 1) = u n := by
    intro n
    apply hmono
    rw [op_comp, Functor.map_comp_apply, hu, hu, ← Functor.map_comp_apply, ← op_comp,
      algHomOver_comp_algebraOverBase]
  obtain ⟨g, hg⟩ := exists_specMap_adic_lift (fun n ↦ (u n).left)
    (fun n ↦ congrArg CommaMorphism.left (hcompat n))
  have hgS : g ≫ U.hom = f := by
    apply specMap_adic_ext
    intro n
    rw [← Category.assoc, hg n, Over.w (u n)]
    rfl
  let G : Over.mk f ⟶ U := Over.homMk g hgS
  have key : ∀ n, F.map (algebraOverBase f (A ⧸ maximalIdeal A ^ (n + 1))).op (F.map G.op ξ) =
      F.map (algebraOverBase f (A ⧸ maximalIdeal A ^ (n + 1))).op η := by
    intro n
    rw [← Functor.map_comp_apply, ← op_comp]
    have : algebraOverBase f (A ⧸ maximalIdeal A ^ (n + 1)) ≫ G = u n :=
      Over.OverMorphism.ext (hg n)
    rw [this, hu]
  refine ⟨G, ?_⟩
  rw [op_id, F.map_id]
  apply (hA A f).1
  intro n
  cases n with
  | zero =>
    rw [← algHomOver_comp_algebraOverBase f (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (I := maximalIdeal A) (Nat.zero_le 1))), op_comp,
      Functor.map_comp_apply, Functor.map_comp_apply, key 0]
    rfl
  | succ n => exact key n

/-! ### Factorization on the spectrum of a local ring -/

/-- The canonical morphism `Spec 𝒪_{T,t} ⟶ T` of an object of `Over S`. -/
def stalkPt (T : Over S) (t : T.left) : Over.mk (T.left.fromSpecStalk t ≫ T.hom) ⟶ T :=
  Over.homMk (T.left.fromSpecStalk t)

/-- SGA 3, XI 3.1, (iii) ⇒ (ii): if `η` factors through `ξ` at the residue field of a point
`t` with noetherian local ring, then `η` factors through `ξ` on `Spec 𝒪_{T,t}`. -/
theorem fac_stalkPt (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    (hét : ∀ y, InfinitesimallyEtaleAt F ξ y) (hA : AdicLimits F) {T : Over S}
    (η : F.obj (op T)) (t : T.left) [IsNoetherianRing (T.left.presheaf.stalk t)]
    (ht : t ∈ W ξ η) : Fac ξ η (stalkPt T t) := by
  let A := T.left.presheaf.stalk t
  let φ : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A))) ≫ T.left.fromSpecStalk t ≫ T.hom) ⟶
      Over.mk (T.left.fromSpecStalk t ≫ T.hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A))))
  have hff : Flat φ.left ∧ Surjective φ.left :=
    (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr
      Module.FaithfullyFlat.of_flat_of_isLocalHom)
  have : Flat φ.left := hff.1
  have : Surjective φ.left := hff.2
  have : QuasiCompact φ.left :=
    (inferInstance : QuasiCompact (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A)))))
  refine fac_of_flat hmono hF φ ?_
  rw [← Category.id_comp (φ ≫ stalkPt T t), ← fac_map_iff]
  apply fac_id_of_isAdicComplete hmono hF hét hA
  refine (mem_W_map_iff hmono hF _ _ _).mpr ?_
  have hpt : (φ ≫ stalkPt T t).left (closedPoint (AdicCompletion (maximalIdeal A) A)) = t :=
    (congrArg (T.left.fromSpecStalk t)
      (specMap_closedPoint (algebraMap A (AdicCompletion (maximalIdeal A) A)))).trans
      Scheme.fromSpecStalk_closedPoint
  exact Set.mem_of_eq_of_mem hpt ht

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing
