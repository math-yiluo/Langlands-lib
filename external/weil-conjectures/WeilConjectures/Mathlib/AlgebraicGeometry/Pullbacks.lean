/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Fibre products of affine schemes over the terminal scheme

`Mathlib.AlgebraicGeometry.Pullbacks` computes the fibre product of `Spec A` and `Spec B` over
`Spec R` as `Spec (A ⊗[R] B)`. Since `Spec (ULift ℤ)` is a terminal scheme, this also computes
the fibre product over the terminal scheme `⊤_ Scheme`, which is the shape in which products of
schemes appear in practice.

## Main declarations

* `AlgebraicGeometry.isPullback_terminalFrom_spec`: the square with projections
  `Spec (A ⊗[ULift ℤ] B) ⟶ Spec A` and `Spec (A ⊗[ULift ℤ] B) ⟶ Spec B` over `⊤_ Scheme` is
  cartesian.
* `AlgebraicGeometry.pullbackTerminalSpecIso`: the induced isomorphism
  `pullback (terminal.from (Spec A)) (terminal.from (Spec B)) ≅ Spec (A ⊗[ULift ℤ] B)`.
* `AlgebraicGeometry.closure_range_mul_appTop_eq_top`: the global sections of a product of two
  affine schemes are generated as a ring by the products of pullbacks of generators of the two
  factors.
* `AlgebraicGeometry.Scheme.Pullback.opensRange_map`: the range of the map of fibre products
  induced by two open immersions is the intersection of the preimages of their ranges, and its
  variant `AlgebraicGeometry.Scheme.Pullback.opensRange_openCoverOfLeftRight_f` for the charts
  of the product of two open covers.
* `AlgebraicGeometry.Scheme.pullback_fst_toSpecΓ_appTop`: global sections of the base change of
  `Spec R ⟶ Spec Γ(U, ⊤)` along `U ⟶ Spec Γ(U, ⊤)`.

Note that `IsAffine (pullback (terminal.from X) (terminal.from Y))` for affine `X` and `Y` is
already an instance in Mathlib, since `⊤_ Scheme` is affine.

## Implementation notes

The `ULift ℤ`-algebra structure on a commutative ring `A : Type u` is `ULift.algebra'`, which is a
def rather than an instance; it is enabled as a local instance in this file.


-/

/-!

# Graphs of partial sections of a fibre product

For a partial section `γ : U ⟶ X ×_S Y` of the first projection, defined on an open
`j : U ⟶ X` and with `Y ⟶ S` separated, the graph of `γ` is a closed immersion
`U ⟶ U ×_S Y`, and the scheme-theoretic image of `γ` restricts over `U ×_S Y` to that
graph.

This is the elimination-of-indeterminacy input for the graph-extension and
common-modification steps of the Nagata compactification proof (Stacks Project
Tags 0F3X–0F3Z; revised blueprint `lemma:nagata-scheme-image-partial-section`).

## Main definitions and results

- `AlgebraicGeometry.partialSection`: the graph `U ⟶ U ×_S Y` of a partial
  section, a closed immersion since `Y ⟶ S` is separated;
- `AlgebraicGeometry.partialSection_openι`: the factorization of `γ` through
  the base-changed open immersion `U ×_S Y ⟶ X ×_S Y`;
- `AlgebraicGeometry.isPullback_partialSectionOpenι` and
  `AlgebraicGeometry.isIso_partialSectionOpenι_restrict`: the base-changed open
  immersion square is cartesian, so `j` being an isomorphism over an open `V ⊆ X`
  makes `U ×_S Y ⟶ X ×_S Y` an isomorphism over the preimage of `V`;
- `AlgebraicGeometry.isPullback_partialSection`: the graph is the pullback of
  `γ` along the base-changed open immersion;
- `AlgebraicGeometry.ker_comap_partialSectionOpenι`: the kernel ideal sheaf of
  `γ` restricted to `U ×_S Y` is the kernel of its graph;
- `AlgebraicGeometry.partialSectionRestrictIso`: the induced isomorphism
  `U ≅ (U ×_S Y) ×_{X ×_S Y} Z` of `U` with the restriction of the scheme-theoretic
  image of `γ` over `U ×_S Y`, compatible with the graph
  (`partialSectionRestrictIso_hom_fst`);
- `AlgebraicGeometry.isIso_morphismRestrict_pullback_fst`: unrelated to partial
  sections, the base change of a partial isomorphism is a partial isomorphism — if
  `g : B ⟶ C` is an isomorphism over an open `O ⊆ C`, then `A ×_C B ⟶ A` is an
  isomorphism over the inverse image of `O`.

-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

namespace AlgebraicGeometry

attribute [local instance] ULift.algebra'

variable (A B : Type u) [CommRing A] [CommRing B]

/-- `Spec (A ⊗[ULift ℤ] B)`, with the two maps induced by `a ↦ a ⊗ₜ 1` and `b ↦ 1 ⊗ₜ b`, is the
fibre product of `Spec A` and `Spec B` over the terminal scheme. -/
theorem isPullback_terminalFrom_spec :
    IsPullback (Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ULift.{u} ℤ) (A := A) (B := B))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom))
      (terminal.from (Spec (.of A))) (terminal.from (Spec (.of B))) := by
  have h : IsPullback (Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ULift.{u} ℤ) (A := A) (B := B))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom))
      (Spec.map (ofHom (algebraMap (ULift.{u} ℤ) A)))
      (Spec.map (ofHom (algebraMap (ULift.{u} ℤ) B))) := ?_
  · exact h.of_isTerminal specULiftZIsTerminal terminalIsTerminal
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso (ULift.{u} ℤ) A B).symm
    (pullbackSpecIso_inv_fst ..) (pullbackSpecIso_inv_snd ..)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp [Algebra.TensorProduct.algebraMap_def]

/-- The fibre product of `Spec A` and `Spec B` over the terminal scheme is
`Spec (A ⊗[ULift ℤ] B)`. -/
noncomputable def pullbackTerminalSpecIso :
    pullback (terminal.from (Spec (.of A))) (terminal.from (Spec (.of B))) ≅
      Spec (.of (A ⊗[ULift.{u} ℤ] B)) :=
  (isPullback_terminalFrom_spec A B).isoPullback.symm

/-- The composition of the inverse of `pullbackTerminalSpecIso A B` with the first projection is
`Spec.map` of the ring morphism `a ↦ a ⊗ₜ 1`. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_inv_fst :
    (pullbackTerminalSpecIso A B).inv ≫ pullback.fst _ _ =
      Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ))) :=
  (isPullback_terminalFrom_spec A B).isoPullback_hom_fst

/-- The composition of the inverse of `pullbackTerminalSpecIso A B` with the second projection is
`Spec.map` of the ring morphism `b ↦ 1 ⊗ₜ b`. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_inv_snd :
    (pullbackTerminalSpecIso A B).inv ≫ pullback.snd _ _ =
      Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom) :=
  (isPullback_terminalFrom_spec A B).isoPullback_hom_snd

/-- The composition of `pullbackTerminalSpecIso A B` with `Spec.map` of the ring morphism
`a ↦ a ⊗ₜ 1` is the first projection. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_hom_fst :
    (pullbackTerminalSpecIso A B).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ))) =
      pullback.fst _ _ := by
  rw [← pullbackTerminalSpecIso_inv_fst, Iso.hom_inv_id_assoc]

/-- The composition of `pullbackTerminalSpecIso A B` with `Spec.map` of the ring morphism
`b ↦ 1 ⊗ₜ b` is the second projection. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_hom_snd :
    (pullbackTerminalSpecIso A B).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
          (A := A) (B := B)).toRingHom) = pullback.snd _ _ := by
  rw [← pullbackTerminalSpecIso_inv_snd, Iso.hom_inv_id_assoc]

/-- **Global sections of a product of two affine schemes are generated by the products of the
pullbacks of generators of the two factors.** -/
theorem closure_range_mul_appTop_eq_top {A B : Type u} [CommRing A] [CommRing B]
    {W : Scheme.{u}} {pa : W ⟶ Spec (.of A)} {pb : W ⟶ Spec (.of B)}
    (hP : IsPullback pa pb (terminal.from _) (terminal.from _))
    {ιA ιB : Type*} {a : ιA → A} {b : ιB → B}
    (ha : Subring.closure (Set.range a) = ⊤) (hb : Subring.closure (Set.range b) = ⊤)
    {ra : ιA} (hra : a ra = 1) {rb : ιB} (hrb : b rb = 1) :
    Subring.closure (Set.range fun p : ιA × ιB ↦
        ((Scheme.ΓSpecIso _).inv ≫ pa.appTop).hom (a p.1) *
          ((Scheme.ΓSpecIso _).inv ≫ pb.appTop).hom (b p.2)) = ⊤ := by
  set e : W ≅ Spec (.of (A ⊗[ULift.{u} ℤ] B)) :=
    hP.isoPullback ≪≫ pullbackTerminalSpecIso A B with he
  set φ : CommRingCat.of (A ⊗[ULift.{u} ℤ] B) ⟶ Γ(W, ⊤) :=
    (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop with hφ
  have hfst : e.hom ≫ Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ULift.{u} ℤ) (A := A) (B := B))) = pa := by
    rw [he, Iso.trans_hom, Category.assoc, pullbackTerminalSpecIso_hom_fst,
      IsPullback.isoPullback_hom_fst]
  have hsnd : e.hom ≫ Spec.map (ofHom (Algebra.TensorProduct.includeRight
      (R := ULift.{u} ℤ) (A := A) (B := B)).toRingHom) = pb := by
    rw [he, Iso.trans_hom, Category.assoc, pullbackTerminalSpecIso_hom_snd,
      IsPullback.isoPullback_hom_snd]
  have hA : ∀ x : A, ((Scheme.ΓSpecIso _).inv ≫ pa.appTop).hom x =
      φ.hom (x ⊗ₜ[ULift.{u} ℤ] 1) := by
    intro x
    rw [← hfst, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← hφ]
    rfl
  have hB : ∀ y : B, ((Scheme.ΓSpecIso _).inv ≫ pb.appTop).hom y =
      φ.hom (1 ⊗ₜ[ULift.{u} ℤ] y) := by
    intro y
    rw [← hsnd, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← hφ]
    rfl
  have hiso : IsIso φ := by rw [hφ]; infer_instance
  have hsurj : Function.Surjective φ.hom :=
    ((ConcreteCategory.isIso_iff_bijective φ).mp hiso).2
  have hrange : ∀ p : ιA × ιB,
      ((Scheme.ΓSpecIso _).inv ≫ pa.appTop).hom (a p.1) *
        ((Scheme.ΓSpecIso _).inv ≫ pb.appTop).hom (b p.2) =
      φ.hom (a p.1 ⊗ₜ[ULift.{u} ℤ] b p.2) := by
    intro p
    rw [hA, hB, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [hrange]
  rw [show (Set.range fun p : ιA × ιB ↦ φ.hom (a p.1 ⊗ₜ[ULift.{u} ℤ] b p.2)) =
      φ.hom '' (Set.range fun p : ιA × ιB ↦ a p.1 ⊗ₜ[ULift.{u} ℤ] b p.2) by
    rw [← Set.range_comp]; rfl]
  rw [← RingHom.map_closure, Algebra.TensorProduct.closure_range_tmul_eq_top ha hb hra hrb]
  ext z
  simp only [Subring.mem_map, Subring.mem_top, iff_true, true_and]
  exact hsurj z

/-- The range of the morphism of fibre products induced by two open immersions `u` and `v` is
the intersection of the preimages of the ranges of `u` and `v`. -/
lemma Scheme.Pullback.opensRange_map {X Y Z X' Y' : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
    (w₁ : (u ≫ f) ≫ 𝟙 Z = u ≫ f) (w₂ : (v ≫ g) ≫ 𝟙 Z = v ≫ g) :
    (pullback.map (u ≫ f) (v ≫ g) f g u v (𝟙 Z) w₁ w₂).opensRange =
      pullback.fst f g ⁻¹ᵁ u.opensRange ⊓ pullback.snd f g ⁻¹ᵁ v.opensRange := by
  set M := pullback.map (u ≫ f) (v ≫ g) f g u v (𝟙 Z) w₁ w₂ with hM
  have hMfst : M ≫ pullback.fst f g = pullback.fst (u ≫ f) (v ≫ g) ≫ u := by simp [hM]
  have hMsnd : M ≫ pullback.snd f g = pullback.snd (u ≫ f) (v ≫ g) ≫ v := by simp [hM]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · change (pullback.fst f g).base (M.base z) ∈ u.opensRange
      rw [← Scheme.Hom.comp_apply, hMfst]
      exact ⟨_, rfl⟩
    · change (pullback.snd f g).base (M.base z) ∈ v.opensRange
      rw [← Scheme.Hom.comp_apply, hMsnd]
      exact ⟨_, rfl⟩
  · set W : (pullback f g).Opens :=
      pullback.fst f g ⁻¹ᵁ u.opensRange ⊓ pullback.snd f g ⁻¹ᵁ v.opensRange with hW
    have h1 : Set.range (W.ι ≫ pullback.fst f g).base ⊆ Set.range u.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2.1
    have h2 : Set.range (W.ι ≫ pullback.snd f g).base ⊆ Set.range v.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2.2
    have hab : IsOpenImmersion.lift u _ h1 ≫ (u ≫ f) =
        IsOpenImmersion.lift v _ h2 ≫ (v ≫ g) := by
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, pullback.condition]
    have hc : pullback.lift _ _ hab ≫ M = W.ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, hMfst, ← Category.assoc, pullback.lift_fst,
          IsOpenImmersion.lift_fac]
      · rw [Category.assoc, hMsnd, ← Category.assoc, pullback.lift_snd,
          IsOpenImmersion.lift_fac]
    rintro y hy
    refine ⟨(pullback.lift _ _ hab).base ⟨y, hy⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hc]
    rfl

/-- The range of the `(i, j)`-th chart of the product cover of a fibre product is the
intersection of the preimages of the `i`-th and `j`-th chart of the two covers. -/
lemma Scheme.Pullback.opensRange_openCoverOfLeftRight_f {X Y Z : Scheme.{u}}
    (𝒰X : X.OpenCover) (𝒰Y : Y.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z) (ij : 𝒰X.I₀ × 𝒰Y.I₀) :
    ((Scheme.Pullback.openCoverOfLeftRight 𝒰X 𝒰Y f g).f ij).opensRange =
      pullback.fst f g ⁻¹ᵁ (𝒰X.f ij.1).opensRange ⊓
        pullback.snd f g ⁻¹ᵁ (𝒰Y.f ij.2).opensRange := by
  rw [← Scheme.Pullback.opensRange_map (f := f) (g := g) (𝒰X.f ij.1) (𝒰Y.f ij.2)
    (by simp) (by simp)]
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange,
    Scheme.Pullback.openCoverOfLeftRight_f]
  rfl

/-- A variant of `AlgebraicGeometry.Scheme.isPullback_of_openCover` in which the pullbacks of the
cover are given by arbitrary pullback squares. -/
lemma Scheme.isPullback_of_openCover_of_isPullback {W Y Z X' : Scheme.{u}}
    (fWX : W ⟶ X') (fWY : W ⟶ Y) (fXZ : X' ⟶ Z) (fYZ : Y ⟶ Z) (𝒰 : X'.OpenCover)
    (W' : 𝒰.I₀ → Scheme.{u}) (a : ∀ i, W' i ⟶ W) (b : ∀ i, W' i ⟶ 𝒰.X i)
    (ha : ∀ i, IsPullback (a i) (b i) fWX (𝒰.f i))
    (H : ∀ i, IsPullback (b i) (a i ≫ fWY) (𝒰.f i ≫ fXZ) fYZ) :
    IsPullback fWX fWY fXZ fYZ := by
  refine Scheme.isPullback_of_openCover fWX fWY fXZ fYZ 𝒰 fun i ↦ ?_
  refine (H i).of_iso (ha i).isoPullback (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Scheme.Cover.pullbackHom]
  · exact (Category.comp_id _).trans (congrArg (· ≫ fWY) (ha i).isoPullback_hom_fst.symm)

end AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {S X Y U : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (j : U ⟶ X)
variable (γ : U ⟶ pullback x y)

/-- The base-changed open immersion `U ×_S Y ⟶ X ×_S Y` induced by `j : U ⟶ X`. -/
def partialSectionOpenι : pullback (j ≫ x) y ⟶ pullback x y :=
  pullback.map (j ≫ x) y x y j (𝟙 Y) (𝟙 S) rfl (by simp)

@[reassoc (attr := simp)]
lemma partialSectionOpenι_fst :
    partialSectionOpenι x y j ≫ pullback.fst x y = pullback.fst (j ≫ x) y ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma partialSectionOpenι_snd :
    partialSectionOpenι x y j ≫ pullback.snd x y = pullback.snd (j ≫ x) y :=
  pullback.lift_snd _ _ _

instance [IsOpenImmersion j] : IsOpenImmersion (partialSectionOpenι x y j) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› inferInstance rfl (by simp)

instance [QuasiCompact j] : QuasiCompact (partialSectionOpenι x y j) :=
  MorphismProperty.pullbackMap (P := @QuasiCompact) ‹_› inferInstance rfl (by simp)

/-- **The base-changed open immersion square is cartesian**: `U ×_S Y` is the fibre
product of `j : U ⟶ X` and the first projection `X ×_S Y ⟶ X`. -/
lemma isPullback_partialSectionOpenι :
    IsPullback (partialSectionOpenι x y j) (pullback.fst (j ≫ x) y)
      (pullback.fst x y) j :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (j ≫ x) y).flip)
    (partialSectionOpenι_fst x y j) (IsPullback.of_hasPullback x y).flip

/-- **The base change of an isomorphism over an open stays an isomorphism**: if
`j : U ⟶ X` restricts to an isomorphism over an open `V ⊆ X` — in the application `j`
is an admissible blow-up and `V` the complement of its center — then the base-changed
morphism `U ×_S Y ⟶ X ×_S Y` restricts to an isomorphism over the preimage of `V`
under the first projection. -/
lemma isIso_partialSectionOpenι_restrict (V : X.Opens) [IsIso (j ∣_ V)] :
    IsIso (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V)) := by
  -- `(U ×_S Y)|_{ρ⁻¹V}` is `U ×_X (X ×_S Y)|_V` by pasting the restriction square onto
  -- the cartesian square above, ...
  have hA : IsPullback (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V))
      (partialSectionOpenι x y j ⁻¹ᵁ (pullback.fst x y ⁻¹ᵁ V)).ι
      (pullback.fst x y ⁻¹ᵁ V).ι (partialSectionOpenι x y j) :=
    isPullback_morphismRestrict _ _
  have hpaste := hA.paste_vert (isPullback_partialSectionOpenι x y j)
  -- ... and `(X ×_S Y)|_V ⟶ X` factors through `V`, so it is `j|_V` base-changed.
  have ht : IsPullback (j ⁻¹ᵁ V).ι (j ∣_ V) j V.ι :=
    (isPullback_morphismRestrict j V).flip
  have hs : IsPullback ((partialSectionOpenι x y j ⁻¹ᵁ (pullback.fst x y ⁻¹ᵁ V)).ι ≫
        pullback.fst (j ≫ x) y)
      (partialSectionOpenι x y j ∣_ (pullback.fst x y ⁻¹ᵁ V)) j
      ((pullback.fst x y ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι]
    exact hpaste.flip
  exact (IsPullback.of_right' hs ht).flip.isIso_fst_of_isIso

variable (hγ : γ ≫ pullback.fst x y = j)

/-- The graph of a partial section `γ` of the first projection over `j : U ⟶ X`: the
induced section `U ⟶ U ×_S Y` of the projection to `U`. -/
def partialSection : U ⟶ pullback (j ≫ x) y :=
  pullback.lift (𝟙 U) (γ ≫ pullback.snd x y)
    (by rw [Category.id_comp, Category.assoc, ← pullback.condition, ← Category.assoc, hγ])

@[reassoc (attr := simp)]
lemma partialSection_fst : partialSection x y j γ hγ ≫ pullback.fst (j ≫ x) y = 𝟙 U :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma partialSection_snd :
    partialSection x y j γ hγ ≫ pullback.snd (j ≫ x) y = γ ≫ pullback.snd x y :=
  pullback.lift_snd _ _ _

/-- The partial section factors through the base-changed open immersion as its
graph. -/
@[reassoc]
lemma partialSection_openι :
    partialSection x y j γ hγ ≫ partialSectionOpenι x y j = γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, partialSectionOpenι_fst, partialSection_fst_assoc, hγ]
  · rw [Category.assoc, partialSectionOpenι_snd, partialSection_snd]

/-- The graph of a partial section of a separated projection is a closed immersion. -/
instance [IsSeparated y] : IsClosedImmersion (partialSection x y j γ hγ) := by
  have : IsSeparated (pullback.fst (j ≫ x) y) :=
    MorphismProperty.pullback_fst _ _ ‹_›
  have : IsClosedImmersion
      (partialSection x y j γ hγ ≫ pullback.fst (j ≫ x) y) := by
    rw [partialSection_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (partialSection x y j γ hγ) (pullback.fst (j ≫ x) y)

/-- A partial section of the first projection over a quasi-compact `j` is itself
quasi-compact: it becomes `j` after composing with the (quasi-separated) first
projection. -/
lemma quasiCompact_of_partialSection [QuasiSeparated y] [QuasiCompact j]
    (hγ : γ ≫ pullback.fst x y = j) : QuasiCompact γ := by
  have : QuasiCompact (γ ≫ pullback.fst x y) := by rw [hγ]; infer_instance
  have : QuasiSeparated (pullback.fst x y) := MorphismProperty.pullback_fst _ _ ‹_›
  exact .of_comp γ (pullback.fst x y)

/-- The graph square: the graph of a partial section is the pullback of `γ` along the
base-changed open immersion `U ×_S Y ⟶ X ×_S Y`. -/
lemma isPullback_partialSection [IsOpenImmersion j] :
    IsPullback (𝟙 U) (partialSection x y j γ hγ) γ (partialSectionOpenι x y j) :=
  IsPullback.of_horiz_isIso_mono
    ⟨by rw [Category.id_comp, partialSection_openι]⟩

section KernelIdentity

variable [IsSeparated y] [IsOpenImmersion j] [QuasiCompact j]

/-- **The scheme-theoretic image of a partial section restricts to its graph**: the
kernel ideal sheaf of `γ` pulled back to `U ×_S Y` is the kernel of the (closed
immersion) graph of `γ`.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`, kernel form.) -/
theorem ker_comap_partialSectionOpenι :
    γ.ker.comap (partialSectionOpenι x y j) = (partialSection x y j γ hγ).ker := by
  have := quasiCompact_of_partialSection x y j γ hγ
  rw [← Scheme.Hom.ker_pullback_snd γ (partialSectionOpenι x y j)]
  have H := isPullback_partialSection x y j γ hγ
  have hsnd : pullback.snd γ (partialSectionOpenι x y j) =
      H.isoPullback.inv ≫ partialSection x y j γ hγ :=
    ((Iso.inv_comp_eq _).mpr H.isoPullback_hom_snd.symm).symm
  rw [hsnd, Scheme.Hom.ker_comp_of_isIso]

/-- The isomorphism of `U` with the restriction of the scheme-theoretic image of a
partial section over `U ×_S Y`: the composite of the identification of `U` with the
image of its graph and the flat base change identification of images.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
def partialSectionRestrictIso : U ≅ pullback (partialSectionOpenι x y j) γ.imageι :=
  asIso (partialSection x y j γ hγ).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (ker_comap_partialSectionOpenι x y j γ hγ).symm) ≪≫
    γ.ker.comapIso (partialSectionOpenι x y j)

/-- The restriction isomorphism is compatible with the graph: composing with the
first projection of the fibre product recovers the graph of the partial section. -/
@[reassoc (attr := simp)]
lemma partialSectionRestrictIso_hom_fst :
    (partialSectionRestrictIso x y j γ hγ).hom ≫
        pullback.fst (partialSectionOpenι x y j) γ.imageι =
      partialSection x y j γ hγ := by
  simp only [partialSectionRestrictIso, Iso.trans_hom, asIso_hom, eqToIso.hom,
    Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  rw [Scheme.IdealSheafData.eqToHom_comp_subschemeι
    (ker_comap_partialSectionOpenι x y j γ hγ).symm]
  exact (partialSection x y j γ hγ).toImage_imageι

/-- The restriction isomorphism is compatible with the canonical morphism to the
scheme-theoretic image: composing with the second projection of the fibre product
recovers `γ.toImage`.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
@[reassoc (attr := simp)]
lemma partialSectionRestrictIso_hom_snd :
    (partialSectionRestrictIso x y j γ hγ).hom ≫
        pullback.snd (partialSectionOpenι x y j) γ.imageι =
      γ.toImage := by
  rw [← cancel_mono γ.imageι, Category.assoc, ← pullback.condition,
    partialSectionRestrictIso_hom_fst_assoc, partialSection_openι, Scheme.Hom.toImage_imageι]

include hγ in
/-- **The fibre of the scheme-theoretic image of a partial section over `j` is `U`
itself**: pulling back the projection `SIm(γ) ⟶ X` of the scheme-theoretic image of a
partial section along the open `j : U ⟶ X` recovers `U`, embedded via the canonical
morphism `γ.toImage`. This is the cartesian form of `partialSectionRestrictIso`.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
lemma isPullback_toImage_partialSection :
    IsPullback γ.toImage (𝟙 U) (γ.imageι ≫ pullback.fst x y) j := by
  -- paste the restriction of the image over `U ×_S Y` onto the cartesian square of the
  -- base-changed open immersion `U ×_S Y ⟶ X ×_S Y` ...
  have hpaste :=
    (IsPullback.of_hasPullback (partialSectionOpenι x y j) γ.imageι).flip.paste_vert
      (isPullback_partialSectionOpenι x y j)
  -- ... and identify the apex with `U` via the restriction isomorphism.
  refine hpaste.of_iso' (partialSectionRestrictIso x y j γ hγ) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp

include hγ in
/-- **The projection of the graph image is an isomorphism over the open part**: the
projection `SIm(γ) ⟶ X` of the scheme-theoretic image of a partial section restricts
to an isomorphism over the range of `j`. This is the isomorphism input for the
elimination of indeterminacy in the graph-extension step (Stacks Project Tag 0F3Z).
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
lemma isIso_restrict_imageι_comp_fst :
    IsIso ((γ.imageι ≫ pullback.fst x y) ∣_ j.opensRange) := by
  -- the graph square, with the `U`-corner rewritten through `j.isoOpensRange`
  have hA : IsPullback γ.toImage j.isoOpensRange.hom (γ.imageι ≫ pullback.fst x y)
      j.opensRange.ι := by
    refine (isPullback_toImage_partialSection x y j γ hγ).of_iso (Iso.refl _) (Iso.refl _)
      j.isoOpensRange (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [Scheme.Hom.isoOpensRange_hom_ι]
  -- the restriction square is a second pullback of the same cospan
  have hB := (isPullback_morphismRestrict (γ.imageι ≫ pullback.fst x y) j.opensRange).flip
  have hcomp : (hA.isoIsPullback _ _ hB).hom ≫
      ((γ.imageι ≫ pullback.fst x y) ∣_ j.opensRange) = j.isoOpensRange.hom :=
    hA.isoIsPullback_hom_snd _ _ hB
  have hiso : IsIso ((hA.isoIsPullback _ _ hB).hom ≫
      ((γ.imageι ≫ pullback.fst x y) ∣_ j.opensRange)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left (hA.isoIsPullback _ _ hB).hom _

end KernelIdentity

section GraphClosure

include hγ in
/-- **The graph of a partial section is closed over the open part**: any point of the
closure of the graph of `γ` lying over the range of `j` (via the first projection)
already lies on the graph. Indeed, over the open locus `pr₁⁻¹(j(U)) = U ×_S Y` the
graph is the closed immersion `partialSection`, so the graph is closed there.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
theorem closure_range_inter_preimage_range_fst_subset [IsSeparated y] [IsOpenImmersion j] :
    closure (Set.range ⇑γ) ∩ ⇑(pullback.fst x y) ⁻¹' Set.range ⇑j ⊆ Set.range ⇑γ := by
  -- the base-changed open immersion `U ×_S Y ⟶ X ×_S Y` has range the locus over `j`
  have hρ : Set.range ⇑(partialSectionOpenι x y j) =
      ⇑(pullback.fst x y) ⁻¹' Set.range ⇑j := by
    apply subset_antisymm
    · rintro - ⟨r, rfl⟩
      refine ⟨pullback.fst (j ≫ x) y r, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, partialSectionOpenι_fst]
    · intro w hw
      have hw' : w ∈ Set.range ⇑(pullback.fst (pullback.fst x y) j) := by
        rw [Scheme.Pullback.range_fst]
        exact hw
      obtain ⟨z, rfl⟩ := hw'
      refine ⟨(isPullback_partialSectionOpenι x y j).isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  -- the graph is a closed immersion into `U ×_S Y`, so its range is the trace on the
  -- open locus of a closed subset `C` of `X ×_S Y`
  have hind := (partialSectionOpenι x y j).isOpenEmbedding.toIsEmbedding.isInducing
  obtain ⟨C, hC, hCim⟩ := hind.image_eq_isClosed_inter_range
    (partialSection x y j γ hγ).isClosedEmbedding.isClosed_range
  have himg : Set.range ⇑γ =
      ⇑(partialSectionOpenι x y j) '' Set.range ⇑(partialSection x y j γ hγ) := by
    conv_lhs => rw [← partialSection_openι x y j γ hγ]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hγrange : Set.range ⇑γ = C ∩ ⇑(pullback.fst x y) ⁻¹' Set.range ⇑j := by
    rw [himg, hCim, hρ]
  -- a limit point of the graph over `j` lies in `C`, hence on the graph
  rintro w ⟨hw₁, hw₂⟩
  rw [hγrange]
  exact ⟨closure_minimal (hγrange.le.trans Set.inter_subset_left) hC hw₁, hw₂⟩

/-- The second-projection form of `closure_range_inter_preimage_range_fst_subset`,
obtained by the symmetry of the fibre product: any point of the closure of the graph of
a partial section of the **second** projection lying over the range of `j'` already
lies on the graph.
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
theorem closure_range_inter_preimage_range_snd_subset (j' : U ⟶ Y)
    [IsSeparated x] [IsOpenImmersion j'] (hγsnd : γ ≫ pullback.snd x y = j') :
    closure (Set.range ⇑γ) ∩ ⇑(pullback.snd x y) ⁻¹' Set.range ⇑j' ⊆ Set.range ⇑γ := by
  have hγ' : (γ ≫ (pullbackSymmetry x y).hom) ≫ pullback.fst y x = j' := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, hγsnd]
  have hcomp : ⇑(γ ≫ (pullbackSymmetry x y).hom) = ⇑(pullbackSymmetry x y).hom ∘ ⇑γ := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
  rintro w ⟨hw₁, hw₂⟩
  -- transport the point along the symmetry homeomorphism
  have hmem : (pullbackSymmetry x y).hom w ∈
      closure (Set.range ⇑(γ ≫ (pullbackSymmetry x y).hom)) ∩
        ⇑(pullback.fst y x) ⁻¹' Set.range ⇑j' := by
    refine ⟨?_, ?_⟩
    · have himage :=
        (Scheme.homeoOfIso (pullbackSymmetry x y)).image_closure (Set.range ⇑γ)
      rw [Scheme.coe_homeoOfIso] at himage
      rw [hcomp, Set.range_comp, ← himage]
      exact Set.mem_image_of_mem _ hw₁
    · have hpt : pullback.fst y x ((pullbackSymmetry x y).hom w) = pullback.snd x y w := by
        rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
      refine Set.mem_preimage.mpr ?_
      rw [hpt]
      exact hw₂
  obtain ⟨t, ht⟩ := closure_range_inter_preimage_range_fst_subset y x j'
    (γ ≫ (pullbackSymmetry x y).hom) hγ' hmem
  refine ⟨t, (Scheme.homeoOfIso (pullbackSymmetry x y)).injective ?_⟩
  rw [Scheme.coe_homeoOfIso, ← Scheme.Hom.comp_apply]
  exact ht

/-- **The graph of a partial section of the second projection is the whole part of its
scheme-theoretic image lying over the open part**: the inverse image in `SIm(γ)` of the
range of `j'` under the second projection is exactly the range of `γ.toImage`. Indeed the
image is the closure of the graph, and over the range of `j'` the graph is already closed
(`closure_range_inter_preimage_range_snd_subset`).
(Revised blueprint: `lemma:nagata-scheme-image-partial-section`.) -/
theorem preimage_range_snd_eq_range_toImage (j' : U ⟶ Y) [IsSeparated x] [IsOpenImmersion j']
    [QuasiCompact γ] (hγsnd : γ ≫ pullback.snd x y = j') :
    ⇑(γ.imageι ≫ pullback.snd x y) ⁻¹' Set.range ⇑j' = Set.range ⇑γ.toImage := by
  apply subset_antisymm
  · intro t ht
    -- the point of `X ×_S Y` under `t` is a limit point of the graph lying over `j'`
    have hcl : γ.imageι t ∈ closure (Set.range ⇑γ) := by
      rw [← Scheme.Hom.support_ker γ, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨t, rfl⟩
    have hsnd : pullback.snd x y (γ.imageι t) ∈ Set.range ⇑j' := by
      rw [← Scheme.Hom.comp_apply]
      exact ht
    obtain ⟨u, hu⟩ := closure_range_inter_preimage_range_snd_subset x y γ j' hγsnd ⟨hcl, hsnd⟩
    refine ⟨u, γ.imageι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι, hu]
  · rintro - ⟨u, rfl⟩
    refine Set.mem_preimage.mpr ⟨u, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Scheme.Hom.toImage_imageι, hγsnd]

end GraphClosure

/-- **The graph image is proper over the base**: if `Y ⟶ S` is proper, the
scheme-theoretic image of a partial section `γ : U ⟶ X ×_S Y`, projected to `X`, is
proper. This is the properness half of the graph-extension lemma: together with
`partialSectionRestrictIso` (the image restricts to `U` over `U ×_S Y`) it yields the
proper extension `SIm(γ) ⟶ X` of the partial section
(Stacks Project Tag 0F3Z; revised blueprint `lemma:nagata-graph-extension`). -/
theorem isProper_imageι_comp_fst [IsProper y] :
    IsProper (γ.imageι ≫ pullback.fst x y) := by
  have : IsProper (pullback.fst x y) := MorphismProperty.pullback_fst _ _ ‹_›
  infer_instance

section RestrictBaseChange

variable {A B C : Scheme.{u}}

/-- **A base change of a partial isomorphism is a partial isomorphism**: if `g : B ⟶ C`
restricts to an isomorphism over an open `O ⊆ C`, then the first projection of the fibre
product `A ×_C B` restricts to an isomorphism over the inverse image of `O` in `A`. -/
lemma isIso_morphismRestrict_pullback_fst (f : A ⟶ C) (g : B ⟶ C) (O : C.Opens)
    [IsIso (g ∣_ O)] : IsIso (pullback.fst f g ∣_ (f ⁻¹ᵁ O)) := by
  have hA : IsPullback (pullback.fst f g ∣_ (f ⁻¹ᵁ O))
      (pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ O)).ι (f ⁻¹ᵁ O).ι (pullback.fst f g) :=
    isPullback_morphismRestrict _ _
  have hpaste := hA.paste_vert (IsPullback.of_hasPullback f g)
  have hs : IsPullback ((pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ O)).ι ≫ pullback.snd f g)
      (pullback.fst f g ∣_ (f ⁻¹ᵁ O)) g ((f ∣_ O) ≫ O.ι) := by
    rw [morphismRestrict_ι]
    exact hpaste.flip
  have ht : IsPullback (g ⁻¹ᵁ O).ι (g ∣_ O) g O.ι := (isPullback_morphismRestrict g O).flip
  exact (IsPullback.of_right' hs ht).flip.isIso_fst_of_isIso

end RestrictBaseChange

section PullbackSpec

/-- For a ring map `φ : Γ(U, ⊤) ⟶ R`, pulling a global function on `U` back to the fibre product
`U ×_{Spec Γ(U, ⊤)} Spec R` along the first projection is the same as applying `φ` and then
pulling back along the second projection: `fst^* = snd^* ∘ (ΓSpecIso R)⁻¹ ∘ φ`. This is the
commutativity of the pullback square on global sections, together with
`X.toSpecΓ.appTop = (ΓSpecIso Γ(X, ⊤)).hom`. -/
lemma Scheme.pullback_fst_toSpecΓ_appTop {U : Scheme.{u}} {R : CommRingCat.{u}}
    (φ : Γ(U, ⊤) ⟶ R) :
    (pullback.fst U.toSpecΓ (Spec.map φ)).appTop =
      φ ≫ (Scheme.ΓSpecIso R).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ)).appTop := by
  have e : (Scheme.ΓSpecIso Γ(U, ⊤)).inv ≫ U.toSpecΓ.appTop = 𝟙 _ := by
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]
  change _ = _ ≫ (pullback.snd U.toSpecΓ (Spec.map φ) ≫ Spec.map φ).appTop
  rw [← pullback.condition]
  change _ = _ ≫ U.toSpecΓ.appTop ≫ (pullback.fst U.toSpecΓ (Spec.map φ)).appTop
  rw [reassoc_of% e]

end PullbackSpec

/-- Two points of a pair of schemes over a common base with the same image come from a point of
any pullback of the pair. -/
lemma _root_.CategoryTheory.IsPullback.exists_scheme_point {P A B C : Scheme.{u}} {fst : P ⟶ A}
    {snd : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) (a : A) (b : B)
    (hab : f a = g b) : ∃ p, fst p = a ∧ snd p = b := by
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  refine ⟨h.isoPullback.inv p, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hp₁]
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hp₂]

end AlgebraicGeometry
