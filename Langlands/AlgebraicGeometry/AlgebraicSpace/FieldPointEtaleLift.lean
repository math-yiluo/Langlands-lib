import Langlands.AlgebraicGeometry.AlgebraicSpace.RationalPointEtaleLiftProof
import Mathlib.FieldTheory.PrimitiveElement

/-! # Field-valued points of algebraic spaces lift to affine étale charts

Let `C` be a ring, `k` a field with a `C`-algebra structure and `X` an algebraic space
over `Spec C`. Every `k`-valued point of `X` is the image of a `k`-valued point of an
actual affine scheme with an étale map to `X`. This is the field-valued-point form of the
lifting result that Conrad cites as Knutson II.6.4; compare Stacks Project Tag 0BBP, which
treats points of `|X|` on decent spaces. No quasi-separatedness or decency is assumed.

The case `C = k` is `RationalPointEtaleLiftProof`. There the Galois group of a finite
Galois extension `K/k` acts on a fibre power of a chart times `Spec K`, which is étale over
the base `Spec k`. Over a general base `Spec C` the scheme `Spec K` is not étale, so here
the fibre power is indexed by the `k`-embeddings `L → K` of the residue field `L` of a
point of the chart over the given point, with `K` the splitting field of the minimal
polynomial of a primitive element of `L`. The Galois group permutes the embeddings
faithfully, hence acts freely on the open subscheme of the fibre power where the
coordinates are pairwise distinct; that open is closed under the action because the
diagonal of an étale chart with separated source is open and closed. The point with
coordinates the embeddings lies in that open, so the quotient of a stable affine
neighbourhood carries a Galois-invariant `K`-point over the given point, which descends
to `k`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap ringTestMap_comp
  ringTestMap_id ringTestMap_left)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace FieldPointEtaleLift

section Galois

variable {C : Type u} [CommRing C] {k : Type u} [Field k] [Algebra C k]
variable {K : Type u} [Field K] [Algebra k K] [Algebra C K] [IsScalarTower C k K]

/-- The map `Spec K → Spec k` over `Spec C`. -/
abbrev fieldTestMap : ringTest C K ⟶ ringTest C k :=
  ringTestMap C (IsScalarTower.toAlgHom C k K)

/-- The Galois group of `K/k` acting on `Spec K` over `Spec C`. -/
def galoisAction : OverAction (K ≃ₐ[k] K) (ringTest C K) where
  act g := ringTestMap C ((g : K →ₐ[k] K).restrictScalars C)
  one := by
    rw [← ringTestMap_id]
    congr 1
  mul g h := by
    rw [← ringTestMap_comp]
    congr 1

theorem galoisAction_act_left (g : K ≃ₐ[k] K) :
    ((galoisAction (C := C)).act g).left =
      Spec.map (CommRingCat.ofHom (g : K →ₐ[k] K).toRingHom) :=
  rfl

instance : Subsingleton (ringTest C K).left :=
  inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))

instance : Nonempty (ringTest C K).left :=
  inferInstanceAs (Nonempty (Spec (CommRingCat.of K)))

/-- The Galois action is compatible with the map to `Spec k`. -/
theorem galoisAction_fieldTestMap (g : K ≃ₐ[k] K) :
    (galoisAction (C := C)).act g ≫ fieldTestMap (C := C) (k := k) (K := K) =
      fieldTestMap := by
  change ringTestMap C _ ≫ ringTestMap C _ = _
  rw [← ringTestMap_comp]
  congr 1
  ext c
  exact g.commutes c

/-- Two morphisms from `Spec k` to an affine scheme agree when they agree after composing
with `Spec K → Spec k`. -/
theorem spec_hom_ext {Z : Scheme.{u}} [IsAffine Z]
    {g₁ g₂ : Spec (CommRingCat.of k) ⟶ Z}
    (h : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ g₁ =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ g₂) : g₁ = g₂ := by
  rw [← cancel_mono Z.isoSpec.hom]
  rw [← cancel_mono Z.isoSpec.hom, Category.assoc, Category.assoc] at h
  rw [← Spec.map_preimage (g₁ ≫ Z.isoSpec.hom), ← Spec.map_preimage (g₂ ≫ Z.isoSpec.hom),
    ← Spec.map_comp, ← Spec.map_comp] at h
  rw [← Spec.map_preimage (g₁ ≫ Z.isoSpec.hom), ← Spec.map_preimage (g₂ ≫ Z.isoSpec.hom)]
  congr 1
  ext a
  exact (algebraMap k K).injective (congrArg (fun g => g.hom a) (Spec.map_injective h))

variable [FiniteDimensional k K] [IsGalois k K]

/-- A `K`-point of an affine scheme over `Spec C` that is invariant under `Gal(K/k)` comes
from a `k`-point. -/
theorem exists_desc_of_galois_invariant {V : Over (Spec (CommRingCat.of C))} [IsAffine V.left]
    (w : ringTest C K ⟶ V) (hw : ∀ σ : K ≃ₐ[k] K, (galoisAction (C := C)).act σ ≫ w = w) :
    ∃ u : ringTest C k ⟶ V, fieldTestMap ≫ u = w := by
  let wl : Spec (CommRingCat.of K) ⟶ V.left := w.left
  let φ : Γ(V.left, ⊤) ⟶ CommRingCat.of K := Spec.preimage (wl ≫ V.left.isoSpec.hom)
  have hφ : Spec.map φ = wl ≫ V.left.isoSpec.hom := Spec.map_preimage _
  have hfix : ∀ (σ : K ≃ₐ[k] K) (a : Γ(V.left, ⊤)), σ (φ a) = φ a := by
    intro σ a
    have hσ : Spec.map (CommRingCat.ofHom (σ : K →ₐ[k] K).toRingHom) ≫ wl = wl :=
      congrArg CommaMorphism.left (hw σ)
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom (σ : K →ₐ[k] K).toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hσ]
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap k K) := fun a =>
    (IsGalois.mem_range_algebraMap_iff_fixed (φ a)).2 fun σ => hfix σ a
  choose c hc using hmem
  have hinj := (algebraMap k K).injective
  let φ' : Γ(V.left, ⊤) →+* k :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, hc, hc, hc, map_mul])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [map_add, hc, hc, hc, map_add]) }
  have hφ' : CommRingCat.ofHom φ' ≫ CommRingCat.ofHom (algebraMap k K) = φ := by
    ext a
    exact hc a
  have hleft : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
      (Spec.map (CommRingCat.ofHom φ') ≫ V.left.isoSpec.inv) = wl := by
    rw [← Category.assoc, ← Spec.map_comp, hφ', hφ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
      ((Spec.map (CommRingCat.ofHom φ') ≫ V.left.isoSpec.inv) ≫ V.hom) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (ringTest C k).hom := by
    rw [← Category.assoc, hleft]
    exact (Over.w w).trans (Over.w (fieldTestMap (C := C) (k := k) (K := K))).symm
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ V.left.isoSpec.inv)
    (spec_hom_ext (K := K) h1), ?_⟩
  exact Over.OverMorphism.ext hleft

omit [IsGalois k K] in
/-- For a finite extension `K/k`, the `k`-points of an algebraic space over `Spec C` inject
into its `K`-points: `Spec K → Spec k` is an fppf cover and the space is an fppf sheaf. -/
theorem changeRing_injective (X : AlgebraicSpace (Spec (CommRingCat.of C))) :
    Function.Injective (RingPoints.changeRing (X := X) (IsScalarTower.toAlgHom C k K)) := by
  intro x₁ x₂ h
  let π : ringTest C K ⟶ ringTest C k := fieldTestMap
  have : Flat π.left := inferInstanceAs (Flat (specOver k K).hom)
  have : LocallyOfFinitePresentation π.left :=
    inferInstanceAs (LocallyOfFinitePresentation (specOver k K).hom)
  have : Surjective π.left := inferInstanceAs (Surjective (specOver k K).hom)
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1 X.toSheaf.property _
    (generate_singleton_mem_fppfTopology π)
  apply hsh.isSeparatedFor.ext
  rintro T f ⟨Z, g, _, ⟨⟩, rfl⟩
  exact (X.pullback_comp g π x₁).trans
    ((congrArg (X.pullback g) h).trans (X.pullback_comp g π x₂).symm)

end Galois

section Embeddings

variable {k : Type u} [Field k]

/-- A nonempty scheme étale over `Spec k` has a point with values in a finite separable
extension of `k` that is a monomorphism of schemes. -/
theorem exists_separable_point_mono (T : Over (Spec (CommRingCat.of k))) [Etale T.hom]
    [Nonempty T.left] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ ∃ w : specOver k L ⟶ T, Mono w.left := by
  obtain ⟨z⟩ := ‹Nonempty T.left›
  obtain ⟨W, hW, hzW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : T.left.Opens) from trivial)
  let A := Γ(T.left, W)
  let ψ : CommRingCat.of k ⟶ A := Spec.preimage (hW.fromSpec ≫ T.hom)
  have hψ : Spec.map ψ = hW.fromSpec ≫ T.hom := Spec.map_preimage _
  let _ : Algebra k A := ψ.hom.toAlgebra
  have het : Algebra.Etale k A := by
    have : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 this)
  have : Nontrivial A := by
    have hz : z ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hzW
    obtain ⟨y, -⟩ := hz
    exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y⟩
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k A).1 het
  have hI : Nonempty I := by
    by_contra hI
    rw [not_nonempty_iff] at hI
    exact not_subsingleton A e.toEquiv.subsingleton
  obtain ⟨i⟩ := hI
  obtain ⟨h₁, h₂⟩ := hAi i
  let j : A →ₐ[k] Ai i := (Pi.evalAlgHom k Ai i).comp e.toAlgHom
  have hj : Function.Surjective j :=
    (Function.surjective_eval i).comp e.surjective
  refine ⟨Ai i, inferInstance, inferInstance, h₁, h₂,
    Over.homMk (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ hW.fromSpec) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ hW.fromSpec) ≫ T.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (Ai i)))
    rw [Category.assoc, ← hψ, ← Spec.map_comp]
    congr 1
    ext c
    exact j.commutes c
  · have : _root_.AlgebraicGeometry.IsClosedImmersion
        (Spec.map (CommRingCat.ofHom j.toRingHom)) :=
      _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
        (CommRingCat.ofHom j.toRingHom) hj
    change Mono (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ hW.fromSpec)
    infer_instance

variable {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- A finite Galois extension `K/k` into which `L` embeds, whose Galois group acts faithfully
on the `k`-embeddings of `L`: the splitting field of the minimal polynomial of a primitive
element of `L`. -/
theorem exists_faithful_galois :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      Finite (L →ₐ[k] K) ∧ Nonempty (L →ₐ[k] K) ∧
      ∀ γ : K ≃ₐ[k] K, (∀ e : L →ₐ[k] K, (γ : K →ₐ[k] K).comp e = e) → γ = 1 := by
  let pb : PowerBasis k L := Field.powerBasisOfFiniteOfSeparable k L
  let f := minpoly k pb.gen
  let K := f.SplittingField
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable k pb.gen
  have hGal : IsGalois k K := IsGalois.of_separable_splitting_field hsep
  have hroot : ∀ r : K, r ∈ f.rootSet K → Polynomial.aeval r f = 0 := fun r hr =>
    (Polynomial.mem_rootSet.mp hr).2
  refine ⟨K, inferInstance, inferInstance, inferInstance, hGal,
    @Finite.of_fintype _ (PowerBasis.AlgHom.fintype pb), ?_, ?_⟩
  · have hdeg : (f.map (algebraMap k K)).degree ≠ 0 := by
      rw [Polynomial.degree_map]
      exact (minpoly.degree_pos pb.isIntegral_gen).ne'
    obtain ⟨r, hr⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero hdeg
    refine ⟨pb.lift r ?_⟩
    rwa [Polynomial.eval_map_algebraMap] at hr
  · intro γ hγ
    have hfix : ∀ r ∈ f.rootSet K, γ r = r := by
      intro r hr
      have h := congrArg (fun e : L →ₐ[k] K => e pb.gen) (hγ (pb.lift r (hroot r hr)))
      simpa [PowerBasis.lift_gen] using h
    have : (γ : K →ₐ[k] K) = AlgHom.id k K :=
      AlgHom.ext_of_adjoin_eq_top (Polynomial.SplittingField.adjoin_rootSet f)
        fun r hr => hfix r hr
    ext x
    exact congrArg (fun φ : K →ₐ[k] K => φ x) this

end Embeddings

section Diagonal

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {V : Over S}
variable (a : (schemeYoneda S).obj V ⟶ X.presheaf)

/-- A section of an étale morphism of schemes is an open immersion. -/
theorem isOpenImmersion_of_section {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Etale f] (s : Z ⟶ Y)
    (hs : s ≫ f = 𝟙 Z) : _root_.AlgebraicGeometry.IsOpenImmersion s := by
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      (pullback.lift (𝟙 Z) s (by simp) : Z ⟶ Limits.pullback (s ≫ f) f) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsOpenImmersion)
      (pullback_lift_diagonal_isPullback s f) inferInstance
  have : IsIso (s ≫ f) := hs ▸ inferInstance
  rw [← Limits.pullback.lift_snd (f := s ≫ f) (g := f) (𝟙 Z) s (by simp)]
  infer_instance

/-- The fibre square `V ×_X V` of the chart `a`. -/
abbrev selfPullback : Over S := (X.representable_from_scheme a).pullback a

/-- The first projection of `V ×_X V`. -/
abbrev selfFst : selfPullback a ⟶ V := Functor.relativelyRepresentable.fst' _ a

/-- The second projection of `V ×_X V`. -/
abbrev selfSnd : selfPullback a ⟶ V := (X.representable_from_scheme a).snd a

theorem selfPullback_isPullback :
    IsPullback ((schemeYoneda S).map (selfFst a)) ((schemeYoneda S).map (selfSnd a)) a a :=
  Functor.relativelyRepresentable.isPullback' _ a

/-- The point of `V ×_X V` given by two points of `V` with equal images in `X`. -/
abbrev selfLift {T : Over S} (y₁ y₂ : T ⟶ V)
    (h : (schemeYoneda S).map y₁ ≫ a = (schemeYoneda S).map y₂ ≫ a) : T ⟶ selfPullback a :=
  Functor.relativelyRepresentable.lift' _ y₁ y₂ h

/-- The diagonal `V → V ×_X V`. -/
abbrev selfDiag : V ⟶ selfPullback a := selfLift a (𝟙 V) (𝟙 V) rfl

theorem selfDiag_fst : selfDiag a ≫ selfFst a = 𝟙 V :=
  Functor.relativelyRepresentable.lift'_fst _ _ _ _

theorem selfDiag_snd : selfDiag a ≫ selfSnd a = 𝟙 V :=
  Functor.relativelyRepresentable.lift'_snd _ _ _ _

/-- A point of `V ×_X V` with equal coordinates factors through the diagonal. -/
theorem eq_selfDiag {T : Over S} (b : T ⟶ selfPullback a)
    (h : b ≫ selfFst a = b ≫ selfSnd a) : b = (b ≫ selfFst a) ≫ selfDiag a :=
  Functor.relativelyRepresentable.hom_ext' _
    (by rw [Category.assoc, selfDiag_fst, Category.comp_id])
    (by rw [Category.assoc, selfDiag_snd, Category.comp_id, h])

/-- The comparison `V ×_X V → V ×_S V` is a monomorphism of schemes. -/
theorem mono_selfPullback_lift :
    Mono (pullback.lift (selfFst a).left (selfSnd a).left
      ((Over.w (selfFst a)).trans (Over.w (selfSnd a)).symm) :
        (selfPullback a).left ⟶ Limits.pullback V.hom V.hom) := by
  constructor
  intro Q g₁ g₂ hg
  have h₁ : g₁ ≫ (selfFst a).left = g₂ ≫ (selfFst a).left := by
    simpa only [Category.assoc, Limits.pullback.lift_fst] using
      congrArg (· ≫ Limits.pullback.fst V.hom V.hom) hg
  have h₂ : g₁ ≫ (selfSnd a).left = g₂ ≫ (selfSnd a).left := by
    simpa only [Category.assoc, Limits.pullback.lift_snd] using
      congrArg (· ≫ Limits.pullback.snd V.hom V.hom) hg
  let T : Over S := Over.mk (g₁ ≫ (selfPullback a).hom)
  have hT : g₂ ≫ (selfPullback a).hom = g₁ ≫ (selfPullback a).hom := by
    rw [← Over.w (selfSnd a), reassoc_of% h₂]
  let f₁ : T ⟶ selfPullback a := Over.homMk g₁
  let f₂ : T ⟶ selfPullback a := Over.homMk g₂ hT
  have : f₁ = f₂ :=
    Functor.relativelyRepresentable.hom_ext' _ (Over.OverMorphism.ext h₁)
      (Over.OverMorphism.ext h₂)
  exact congrArg CommaMorphism.left this

/-- The diagonal of an étale chart with separated source is an open immersion. -/
theorem isOpenImmersion_selfDiag (ha : IsEtale a) :
    _root_.AlgebraicGeometry.IsOpenImmersion (selfDiag a).left := by
  have : Etale (selfFst a).left := ha.projection a _ _ (selfPullback_isPullback a).flip
  exact isOpenImmersion_of_section (selfFst a).left (selfDiag a).left
    (by rw [← Over.comp_left, selfDiag_fst, Over.id_left])

/-- The diagonal of a chart with separated source is a closed immersion. -/
theorem isClosedImmersion_selfDiag [_root_.AlgebraicGeometry.IsSeparated V.hom] :
    _root_.AlgebraicGeometry.IsClosedImmersion (selfDiag a).left := by
  have := mono_selfPullback_lift a
  have hfst : (selfFst a).left = pullback.lift (selfFst a).left (selfSnd a).left
      ((Over.w (selfFst a)).trans (Over.w (selfSnd a)).symm) ≫
        Limits.pullback.fst V.hom V.hom := (Limits.pullback.lift_fst _ _ _).symm
  have : _root_.AlgebraicGeometry.IsSeparated (selfFst a).left := by
    rw [hfst]
    infer_instance
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((selfDiag a).left ≫ (selfFst a).left) := by
    rw [← Over.comp_left, selfDiag_fst, Over.id_left]
    infer_instance
  exact _root_.AlgebraicGeometry.IsClosedImmersion.of_comp _ (selfFst a).left

end Diagonal

section Distinct

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {V : Over S}
variable {a : (schemeYoneda S).obj V ⟶ X.presheaf} {E : Type u} [Finite E]
variable (Y : ChartFibrePower a E)

/-- The pair of coordinates `e, e'` of the fibre power, as a point of `V ×_X V`. -/
abbrev coordPair (e e' : E) : Y.obj ⟶ selfPullback a :=
  selfLift a (Y.pr e) (Y.pr e') (Y.w e e')

omit [Finite E] in
@[reassoc]
theorem coordPair_fst (e e' : E) : coordPair Y e e' ≫ selfFst a = Y.pr e :=
  Functor.relativelyRepresentable.lift'_fst _ _ _ _

omit [Finite E] in
@[reassoc]
theorem coordPair_snd (e e' : E) : coordPair Y e e' ≫ selfSnd a = Y.pr e' :=
  Functor.relativelyRepresentable.lift'_snd _ _ _ _

/-- The open subscheme of the fibre power where distinct coordinates are distinct. -/
def distinctLocus [_root_.AlgebraicGeometry.IsSeparated V.hom] : Y.obj.left.Opens :=
  ⨅ p : {p : E × E // p.1 ≠ p.2}, (coordPair Y p.1.1 p.1.2).left ⁻¹ᵁ
    ⟨(Set.range (selfDiag a).left)ᶜ, by
      have := isClosedImmersion_selfDiag a
      exact (selfDiag a).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

theorem mem_distinctLocus [_root_.AlgebraicGeometry.IsSeparated V.hom] {x : Y.obj.left} :
    x ∈ distinctLocus Y ↔ ∀ e e' : E, e ≠ e' →
      (coordPair Y e e').left x ∉ Set.range (selfDiag a).left := by
  rw [distinctLocus, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  constructor
  · intro h e e' hee'
    exact h ⟨(e, e'), hee'⟩
  · intro h p
    exact h p.1.1 p.1.2 p.2

/-- Points of the distinct locus valued in nonempty schemes have distinct coordinates. -/
theorem ne_of_mem_distinctLocus [_root_.AlgebraicGeometry.IsSeparated V.hom]
    {T : Over S} [Nonempty T.left] (b : T ⟶ Y.obj)
    (hb : ∀ t, b.left t ∈ distinctLocus Y) {e e' : E} (hee' : e ≠ e') :
    b ≫ Y.pr e ≠ b ≫ Y.pr e' := by
  intro h
  obtain ⟨t⟩ := ‹Nonempty T.left›
  have hpair : b ≫ coordPair Y e e' = (b ≫ Y.pr e) ≫ selfDiag a := by
    refine (eq_selfDiag a _ ?_).trans ?_
    · rw [Category.assoc, Category.assoc, coordPair_fst, coordPair_snd, h]
    · simp only [Category.assoc, coordPair_fst_assoc]
  apply (mem_distinctLocus Y).1 (hb t) e e' hee'
  refine ⟨(b ≫ Y.pr e).left t, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← hpair, Over.comp_left,
    Scheme.Hom.comp_apply]

/-- A point from a one-point scheme with pairwise distinct coordinates lies in the distinct
locus. -/
theorem mem_distinctLocus_of_ne [_root_.AlgebraicGeometry.IsSeparated V.hom] (ha : IsEtale a)
    {T : Over S} [Subsingleton T.left] (b : T ⟶ Y.obj)
    (hb : ∀ e e', e ≠ e' → b ≫ Y.pr e ≠ b ≫ Y.pr e') (t : T.left) :
    b.left t ∈ distinctLocus Y := by
  have := isOpenImmersion_selfDiag a ha
  rw [mem_distinctLocus]
  intro e e' hee' hmem
  have hrange : Set.range (b ≫ coordPair Y e e').left ⊆ Set.range (selfDiag a).left := by
    rintro _ ⟨t', rfl⟩
    rw [Subsingleton.elim t' t, Over.comp_left, Scheme.Hom.comp_apply]
    exact hmem
  let m := _root_.AlgebraicGeometry.IsOpenImmersion.lift (selfDiag a).left
    (b ≫ coordPair Y e e').left hrange
  have hm : m ≫ (selfDiag a).left = (b ≫ coordPair Y e e').left :=
    _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have h₁ : (b ≫ Y.pr e).left = m := by
    have e₁ : (b ≫ coordPair Y e e' ≫ selfFst a).left = (b ≫ Y.pr e).left := by
      rw [coordPair_fst]
    rw [← e₁, ← Category.assoc, Over.comp_left, ← hm, Category.assoc, ← Over.comp_left,
      selfDiag_fst, Over.id_left, Category.comp_id]
  have h₂ : (b ≫ Y.pr e').left = m := by
    have e₂ : (b ≫ coordPair Y e e' ≫ selfSnd a).left = (b ≫ Y.pr e').left := by
      rw [coordPair_snd]
    rw [← e₂, ← Category.assoc, Over.comp_left, ← hm, Category.assoc, ← Over.comp_left,
      selfDiag_snd, Over.id_left, Category.comp_id]
  exact hb e e' hee' (Over.OverMorphism.ext (h₁.trans h₂.symm))

end Distinct

section Actions

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {V : Over S}
variable {a : (schemeYoneda S).obj V ⟶ X.presheaf}
variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]
variable {K : Type u} [Field K] [Algebra k K]

theorem one_comp_emb (e : L →ₐ[k] K) : ((1 : K ≃ₐ[k] K) : K →ₐ[k] K).comp e = e :=
  AlgHom.ext fun _ => rfl

theorem mul_comp_emb (g h : K ≃ₐ[k] K) (e : L →ₐ[k] K) :
    ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K).comp e =
      (g : K →ₐ[k] K).comp ((h : K →ₐ[k] K).comp e) :=
  AlgHom.ext fun _ => rfl

/-- The Galois group of `K/k` acts on the fibre power indexed by the `k`-embeddings `L → K`
by composing the index: `act γ ≫ pr e = pr (γ ∘ e)`. -/
def embAction (Y : ChartFibrePower a (L →ₐ[k] K)) : OverAction (K ≃ₐ[k] K) Y.obj where
  act γ := Y.lift (fun e => Y.pr ((γ : K →ₐ[k] K).comp e)) fun _ _ => Y.w _ _
  one := Y.hom_ext _ _ fun e => by simp only [Y.lift_pr, Category.id_comp, one_comp_emb]
  mul g h := Y.hom_ext _ _ fun e => by
    simp only [Category.assoc, Y.lift_pr, mul_comp_emb]

theorem embAction_pr (Y : ChartFibrePower a (L →ₐ[k] K)) (γ : K ≃ₐ[k] K) (e : L →ₐ[k] K) :
    (embAction Y).act γ ≫ Y.pr e = Y.pr ((γ : K →ₐ[k] K).comp e) :=
  Y.lift_pr _ _ e

variable {G : Type u} [Group G] {Z : Over S}

/-- The restriction of an action to a stable open, as an action over the base. -/
def resAction (ρ : OverAction G Z) (U : Z.left.Opens)
    (hU : ∀ g, (ρ.act g).left ⁻¹ᵁ U = U) : OverAction G (OverAction.resOver U) where
  act g := Over.homMk (ρ.resAct U hU g) (by
    change ρ.resAct U hU g ≫ (OverAction.resOverι U).left ≫ Z.hom =
      (OverAction.resOverι U).left ≫ Z.hom
    rw [OverAction.resAct_ι_assoc, Over.w])
  one := Over.OverMorphism.ext (ρ.resAct_one U hU)
  mul g h := Over.OverMorphism.ext (ρ.resAct_mul U hU g h)

theorem resAction_ι (ρ : OverAction G Z) (U : Z.left.Opens)
    (hU : ∀ g, (ρ.act g).left ⁻¹ᵁ U = U) (g : G) :
    (resAction ρ U hU).act g ≫ OverAction.resOverι U = OverAction.resOverι U ≫ ρ.act g :=
  Over.OverMorphism.ext (ρ.resAct_ι U hU g)

end Actions

section Lift

variable {C : Type u} [CommRing C] {k : Type u} [Field k] [Algebra C k]

/-- **Field-valued points lift to affine étale charts** (compare Knutson II.6.4 and Stacks
Tag 0BBP). Let `k` be a field with a `C`-algebra structure. Every `k`-valued point of an
algebraic space over `Spec C` is the image of a `k`-valued point of an actual affine scheme
with an étale map to the space. -/
theorem exists_affine_etale_point (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (x : RingPoints C X k) :
    ∃ (U : Over (Spec (CommRingCat.of C))) (f : (schemeToSpace _).obj U ⟶ X),
      IsAffine U.left ∧ IsEtale (hom f) ∧
        ∃ u : RingPoint C U k, RingPoints.map f ((schemeRingPointsEquiv C U k).symm u) = x := by
  -- the fibre of an atlas over `x`, a nonempty scheme étale over `Spec k`
  obtain ⟨U₀, a₀, ha₀, he₀, hs₀⟩ := X.exists_atlas
  let xh : (schemeYoneda (Spec (CommRingCat.of C))).obj (ringTest C k) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm x
  let P := ha₀.pullback xh
  let p : P ⟶ ringTest C k := ha₀.snd xh
  let q : P ⟶ U₀ := Functor.relativelyRepresentable.fst' ha₀ xh
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a₀ xh :=
    Functor.relativelyRepresentable.isPullback' ha₀ xh
  have hpe : Etale p.left := he₀.projection xh _ p hsq
  have hps : Surjective p.left := hs₀.projection xh _ p hsq
  let T : Over (Spec (CommRingCat.of k)) := Over.mk p.left
  have : Etale T.hom := hpe
  have : Nonempty T.left := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    obtain ⟨z, -⟩ := hps.surj y
    exact ⟨z⟩
  -- a point of the fibre with values in a finite separable extension `L`, and a Galois
  -- extension `K` acting faithfully on the embeddings `L → K`
  obtain ⟨L, _, _, hL, hLs, w₀, hw₀⟩ := exists_separable_point_mono T
  have := hL
  have := hLs
  have := hw₀
  obtain ⟨K, _, _, hK, hKg, hEfin, hEne, hfaith⟩ := exists_faithful_galois (k := k) (L := L)
  have := hK
  have := hKg
  have := hEfin
  let _ : Algebra C L := ((algebraMap k L).comp (algebraMap C k)).toAlgebra
  have : IsScalarTower C k L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra C K := ((algebraMap k K).comp (algebraMap C k)).toAlgebra
  have : IsScalarTower C k K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let w₀l : (ringTest C L).left ⟶ P.left := w₀.left
  have hw₀p : w₀l ≫ p.left = (fieldTestMap (C := C) (k := k) (K := L)).left := Over.w w₀
  have : Mono w₀l := hw₀
  let w₁ : ringTest C L ⟶ P := Over.homMk w₀l (by
    rw [← Over.w p, ← Category.assoc, hw₀p]
    exact Over.w (fieldTestMap (C := C) (k := k) (K := L)))
  have hw₁p : w₁ ≫ p = fieldTestMap (C := C) (k := k) (K := L) := Over.OverMorphism.ext hw₀p
  let wE : (L →ₐ[k] K) → (ringTest C K ⟶ P) := fun e => ringTestMap C (e.restrictScalars C) ≫ w₁
  have hwp : ∀ e, wE e ≫ p = fieldTestMap := by
    intro e
    change (ringTestMap C (e.restrictScalars C) ≫ w₁) ≫ p = _
    rw [Category.assoc, hw₁p, ← ringTestMap_comp]
    congr 1
    ext c
    exact e.commutes c
  -- an affine open neighbourhood `V` of the image in the atlas
  let v₁ : ringTest C L ⟶ U₀ := w₁ ≫ q
  obtain ⟨y₀⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  obtain ⟨O, hO, hyO, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show v₁.left y₀ ∈ (⊤ : U₀.left.Opens) from trivial)
  have : IsAffine (OverAction.resOver O).left := hO
  have : _root_.AlgebraicGeometry.IsSeparated (OverAction.resOver O).hom := inferInstance
  have hrange : Set.range v₁.left ⊆ Set.range (OverAction.resOverι O).left := by
    rintro _ ⟨y', rfl⟩
    rw [Subsingleton.elim y' y₀]
    exact ⟨⟨v₁.left y₀, hyO⟩, Scheme.Opens.ι_apply _ _⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ringTest C L ⟶ OverAction.resOver O,
      ℓ ≫ OverAction.resOverι O = v₁ := by
    let ℓ' := _root_.AlgebraicGeometry.IsOpenImmersion.lift (OverAction.resOverι O).left
      v₁.left hrange
    have hℓ' : ℓ' ≫ (OverAction.resOverι O).left = v₁.left :=
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange
    refine ⟨Over.homMk ℓ' ?_, Over.OverMorphism.ext hℓ'⟩
    change ℓ' ≫ (OverAction.resOverι O).left ≫ U₀.hom = (ringTest C L).hom
    rw [reassoc_of% hℓ', Over.w v₁]
  obtain ⟨a, ha_def⟩ : ∃ a : (schemeYoneda _).obj (OverAction.resOver O) ⟶ X.presheaf,
      a = (schemeYoneda _).map (OverAction.resOverι O) ≫ a₀ := ⟨_, rfl⟩
  have ha : IsEtale a := by
    rw [ha_def]
    exact IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale O.ι))) he₀
  -- the `K`-points of `V` given by the embeddings `L → K`
  let vE : (L →ₐ[k] K) → (ringTest C K ⟶ OverAction.resOver O) :=
    fun e => ringTestMap C (e.restrictScalars C) ≫ ℓ
  have hvι : ∀ e, vE e ≫ OverAction.resOverι O = wE e ≫ q := fun e => by
    change (ringTestMap C (e.restrictScalars C) ≫ ℓ) ≫ _ =
      (ringTestMap C (e.restrictScalars C) ≫ w₁) ≫ q
    rw [Category.assoc, hℓ, Category.assoc]
  have hvE : ∀ e, (schemeYoneda _).map (vE e) ≫ a =
      (schemeYoneda _).map (fieldTestMap (C := C) (k := k) (K := K)) ≫ xh := fun e => by
    rw [ha_def, ← Functor.map_comp_assoc, hvι, Functor.map_comp_assoc, hsq.w,
      ← Functor.map_comp_assoc, hwp]
  have hvinj : Function.Injective vE := by
    intro e e' hee
    have hq : wE e ≫ q = wE e' ≫ q := by rw [← hvι, ← hvι, hee]
    have hw : wE e = wE e' :=
      Functor.relativelyRepresentable.hom_ext' ha₀ hq (by rw [hwp, hwp])
    have h1 : (ringTestMap C (e.restrictScalars C)).left ≫ w₀l =
        (ringTestMap C (e'.restrictScalars C)).left ≫ w₀l := congrArg CommaMorphism.left hw
    rw [cancel_mono, ringTestMap_left, ringTestMap_left] at h1
    have h2 := Spec.map_injective h1
    ext x
    exact congrArg (fun φ => φ.hom x) h2
  -- the fibre power of `V` indexed by the embeddings, with the Galois action
  have := hEne
  obtain ⟨Y, hYsep, hYet⟩ := ChartFibrePower.exists_of_finite ha (L →ₐ[k] K)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : OverAction (K ≃ₐ[k] K) Y.obj,
      ∀ γ e, ρ.act γ ≫ Y.pr e = Y.pr ((γ : K →ₐ[k] K).comp e) :=
    ⟨embAction Y, embAction_pr Y⟩
  obtain ⟨y, hy⟩ : ∃ y : ringTest C K ⟶ Y.obj, ∀ e, y ≫ Y.pr e = vE e :=
    ⟨Y.lift vE fun e e' => by rw [hvE, hvE], Y.lift_pr _ _⟩
  have hyeq : ∀ γ : K ≃ₐ[k] K, y ≫ ρ.act γ = (galoisAction (C := C)).act γ ≫ y := by
    intro γ
    refine Y.hom_ext _ _ fun e => ?_
    rw [Category.assoc, hρ, hy, Category.assoc, hy]
    change ringTestMap C (((γ : K →ₐ[k] K).comp e).restrictScalars C) ≫ ℓ =
      ringTestMap C ((γ : K →ₐ[k] K).restrictScalars C) ≫
        ringTestMap C (e.restrictScalars C) ≫ ℓ
    rw [← Category.assoc, ← ringTestMap_comp]
    exact congrArg (· ≫ ℓ) (congrArg (ringTestMap C) (AlgHom.ext fun _ => rfl))
  -- the stable open where the coordinates are pairwise distinct; the action is free there
  obtain ⟨W, hW, hWD, hWmem⟩ : ∃ W : Y.obj.left.Opens, (∀ g, (ρ.act g).left ⁻¹ᵁ W = W) ∧
      (∀ s ∈ W, s ∈ distinctLocus Y) ∧
        ∀ s, (∀ g, (ρ.act g).left s ∈ distinctLocus Y) → s ∈ W := by
    refine ⟨ρ.orbitInf (distinctLocus Y), ρ.preimage_orbitInf _, fun s hs => ?_,
      fun s hs => ρ.mem_orbitInf.2 hs⟩
    have h := ρ.mem_orbitInf.1 hs 1
    rw [ρ.one, Over.id_left] at h
    exact h
  obtain ⟨τ, hτ⟩ : ∃ τ : OverAction (K ≃ₐ[k] K) (OverAction.resOver W),
      ∀ g, τ.act g ≫ OverAction.resOverι W = OverAction.resOverι W ≫ ρ.act g :=
    ⟨resAction ρ W hW, resAction_ι ρ W hW⟩
  have hfree : τ.IsFree := by
    intro Tq _ b g h hgh
    have hgh' : b ≫ (τ.act g).left = b ≫ (τ.act h).left := hgh
    let c : Tq ⟶ Y.obj.left := b ≫ (OverAction.resOverι W).left
    have hc : ∀ γ, b ≫ (τ.act γ).left ≫ (OverAction.resOverι W).left =
        c ≫ (ρ.act γ).left := fun γ => by
      rw [← Over.comp_left, hτ, Over.comp_left, ← Category.assoc]
    have hcgh : c ≫ (ρ.act g).left = c ≫ (ρ.act h).left := by
      rw [← hc, ← hc, reassoc_of% hgh']
    let T' : Over (Spec (CommRingCat.of C)) := Over.mk (c ≫ Y.obj.hom)
    have : Nonempty T'.left := ‹Nonempty Tq›
    let b' : T' ⟶ Y.obj := Over.homMk c rfl
    have hb' : ∀ t, b'.left t ∈ distinctLocus Y := fun t => hWD _ (by
      change (b ≫ (OverAction.resOverι W).left) t ∈ W
      rw [Scheme.Hom.comp_apply]
      exact (b t).2)
    have hpr : ∀ e : L →ₐ[k] K, (g : K →ₐ[k] K).comp e = (h : K →ₐ[k] K).comp e := by
      intro e
      by_contra hne
      apply ne_of_mem_distinctLocus Y b' hb' hne
      have hb'gh : b' ≫ ρ.act g = b' ≫ ρ.act h := Over.OverMorphism.ext hcgh
      rw [← hρ, ← hρ, reassoc_of% hb'gh]
    have h1 : g⁻¹ * h = 1 := hfaith _ fun e => by
      ext x
      have hx : g (e x) = h (e x) := congrArg (fun f : L →ₐ[k] K => f x) (hpr e)
      change (g⁻¹ * h) (e x) = e x
      rw [AlgEquiv.mul_apply, ← hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact inv_mul_eq_one.1 h1
  have : _root_.AlgebraicGeometry.IsSeparated Y.obj.hom := hYsep
  have : _root_.AlgebraicGeometry.IsSeparated (OverAction.resOver W).hom := by
    change _root_.AlgebraicGeometry.IsSeparated (W.ι ≫ Y.obj.hom)
    infer_instance
  have : (OverAction.resOver W).left.IsSeparated :=
    ⟨by rw [← terminal.comp_from (OverAction.resOver W).hom]; infer_instance⟩
  -- the invariant étale map from the stable open, and the equivariant point
  obtain ⟨e₀⟩ := hEne
  obtain ⟨t, rfl⟩ : ∃ t : (schemeYoneda _).obj (OverAction.resOver W) ⟶ X.presheaf,
      t = (schemeYoneda _).map (OverAction.resOverι W ≫ Y.pr e₀) ≫ a := ⟨_, rfl⟩
  have ht : IsEtale ((schemeYoneda _).map (OverAction.resOverι W ≫ Y.pr e₀) ≫ a) := by
    refine IsEtale.comp (isEtale_map _ ?_) ha
    have := hYet e₀
    rw [Over.comp_left]
    infer_instance
  have hinv : ∀ g, (schemeYoneda _).map (τ.act g) ≫
      (schemeYoneda _).map (OverAction.resOverι W ≫ Y.pr e₀) ≫ a =
        (schemeYoneda _).map (OverAction.resOverι W ≫ Y.pr e₀) ≫ a := by
    intro g
    rw [← Functor.map_comp_assoc, ← Category.assoc, hτ, Category.assoc, hρ,
      Functor.map_comp_assoc, Functor.map_comp_assoc, Y.w ((g : K →ₐ[k] K).comp e₀) e₀]
  have hyW : ∀ s, y.left s ∈ W := by
    intro s
    refine hWmem _ fun g => ?_
    have hb : ∀ e e', e ≠ e' → (y ≫ ρ.act g) ≫ Y.pr e ≠ (y ≫ ρ.act g) ≫ Y.pr e' := by
      intro e e' hee' h
      rw [Category.assoc, hρ, hy, Category.assoc, hρ, hy] at h
      apply hee'
      ext x
      exact g.injective (congrArg (fun f : L →ₐ[k] K => f x) (hvinj h))
    have := mem_distinctLocus_of_ne Y ha (y ≫ ρ.act g) hb s
    rwa [Over.comp_left, Scheme.Hom.comp_apply] at this
  have hrangeW : Set.range y.left ⊆ Set.range (OverAction.resOverι W).left := by
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨y.left s, hyW s⟩, Scheme.Opens.ι_apply _ _⟩
  obtain ⟨z, hz⟩ : ∃ z : ringTest C K ⟶ OverAction.resOver W,
      z ≫ OverAction.resOverι W = y := by
    let z₁ := _root_.AlgebraicGeometry.IsOpenImmersion.lift (OverAction.resOverι W).left
      y.left hrangeW
    have hz₁ : z₁ ≫ (OverAction.resOverι W).left = y.left :=
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrangeW
    refine ⟨Over.homMk z₁ ?_, Over.OverMorphism.ext hz₁⟩
    change z₁ ≫ (OverAction.resOverι W).left ≫ Y.obj.hom = (ringTest C K).hom
    rw [reassoc_of% hz₁, Over.w y]
  have hzeq : ∀ g, z ≫ τ.act g = (galoisAction (C := C)).act g ≫ z := by
    intro g
    have h : (z ≫ τ.act g) ≫ OverAction.resOverι W =
        ((galoisAction (C := C)).act g ≫ z) ≫ OverAction.resOverι W := by
      rw [Category.assoc, hτ, ← Category.assoc, hz, Category.assoc, hz, hyeq]
    have h' := congrArg CommaMorphism.left h
    simp only [Over.comp_left] at h'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [← cancel_mono (OverAction.resOverι W).left]
    simpa only [Category.assoc] using h'
  -- the affine quotient chart, and descent of the invariant `K`-point to `k`
  obtain ⟨M, tM, w, hM, htM, hw, hwt⟩ :=
    OverAction.exists_affine_chart_of_point X τ (galoisAction (C := C) (k := k) (K := K)) hfree
      _ ht hinv z hzeq
  have := hM
  obtain ⟨u, hu⟩ := exists_desc_of_galois_invariant w hw
  have hfinal : (schemeYoneda _).map w ≫ tM =
      (schemeYoneda _).map (fieldTestMap (C := C) (k := k) (K := K)) ≫ xh := by
    rw [hwt, ← Functor.map_comp_assoc, ← Category.assoc, hz, hy, hvE]
  refine ⟨M, AlgebraicSpace.homMk tM, hM, htM, u, ?_⟩
  apply changeRing_injective (K := K) X
  have e₁ : RingPoints.map (AlgebraicSpace.homMk tM : (schemeToSpace _).obj M ⟶ X)
      ((schemeRingPointsEquiv C M k).symm u) =
        uliftYonedaEquiv ((schemeYoneda _).map u ≫ tM) := by
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    rfl
  have e₂ : x = uliftYonedaEquiv
      (uliftYonedaEquiv.symm x : (schemeYoneda _).obj (ringTest C k) ⟶ X.presheaf) :=
    (Equiv.apply_symm_apply _ _).symm
  rw [e₁, e₂]
  change X.presheaf.map (fieldTestMap (C := C) (k := k) (K := K)).op _ =
    X.presheaf.map (fieldTestMap (C := C) (k := k) (K := K)).op _
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
  congr 1
  rw [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, hu]
  exact hfinal

end Lift

end FieldPointEtaleLift

end Langlands.AlgebraicGeometry.AlgebraicSpace
