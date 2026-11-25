/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Properties of cofiltered limits of schemes affine over a base

Let `{Dᵢ}` be a cofiltered diagram of schemes with affine transition morphisms, with a limit
cone `c`, and let `pᵢ : Dᵢ ⟶ S` be compatible morphisms to a base scheme `S`, inducing
`q : lim Dᵢ ⟶ S`. We record:

- `AlgebraicGeometry.Scheme.ext_of_isLimit`: points of `lim Dᵢ` are determined by their images in
  the stages (the preimages of opens of the stages form a basis, Stacks Project Tag 01Z4, and
  schemes are `T₀`).
- `AlgebraicGeometry.Scheme.isLimitPullbackCone`: base change along `T ⟶ S` commutes with the
  limit: `T ×_S lim Dᵢ = lim (T ×_S Dᵢ)`.
- `AlgebraicGeometry.Scheme.isLimitPairCone`: `lim Dᵢ ×_S lim Dᵢ = lim (Dᵢ ×_S Dᵢ)`.
- `AlgebraicGeometry.Scheme.surjective_of_isLimit`: if all `pᵢ` are affine and surjective, so is
  `q` (Stacks Project Tag 01Z2 applied to the fibres).
- `AlgebraicGeometry.Scheme.weaklyEtale_of_isLimit`: if all `pᵢ` are affine and étale, then `q`
  is weakly étale, being pro-(affine étale) over every affine open of `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) {c : Cone D} (hc : IsLimit c)

include hc in
/-- **Points of a cofiltered limit with affine transition maps are determined by their images
in the stages**: the preimages of the affine opens of the stages form a basis of the topology
of `lim Dᵢ` (Stacks Project Tag 01Z4), and schemes are `T₀`. -/
theorem ext_of_isLimit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    {x y : c.pt} (h : ∀ i, c.π.app i x = c.π.app i y) : x = y := by
  refine Inseparable.eq ((isBasis_preimage_isAffineOpen D c hc).inseparable_iff.mpr ?_)
  rintro _ ⟨_, ⟨i, V, -, rfl⟩, rfl⟩
  change c.π.app i x ∈ V ↔ c.π.app i y ∈ V
  rw [h i]

variable {S : Scheme.{u}} (p : ∀ i, D.obj i ⟶ S)
  (hp : ∀ {i j : I} (f : i ⟶ j), D.map f ≫ p j = p i) (q : c.pt ⟶ S)
  (hq : ∀ i, c.π.app i ≫ p i = q)

section Pullback

variable {T : Scheme.{u}} (g : T ⟶ S)

/-- The diagram `i ↦ Dᵢ ×_S T` of base changes along `g : T ⟶ S`. -/
@[simps]
noncomputable abbrev pullbackDiagram : I ⥤ Scheme.{u} where
  obj i := pullback (p i) g
  map {i j} f := pullback.map (p i) g (p j) g (D.map f) (𝟙 T) (𝟙 S) (by simp [hp]) (by simp)
  map_id i := by ext <;> simp
  map_comp f f' := by ext <;> simp

/-- The cone over the base changes `Dᵢ ×_S T` with point `lim Dᵢ ×_S T`. -/
@[simps]
noncomputable abbrev pullbackCone : Cone (pullbackDiagram D p hp g) where
  pt := pullback q g
  π :=
    { app i := pullback.map q g (p i) g (c.π.app i) (𝟙 T) (𝟙 S) (by simp [hq]) (by simp)
      naturality i j f := by
        refine (Category.id_comp _).trans ?_
        ext <;> simp }

include hc hq in
/-- **Base change commutes with cofiltered limits**: `lim Dᵢ ×_S T = lim (Dᵢ ×_S T)`. -/
noncomputable def isLimitPullbackCone [IsCofiltered I] :
    IsLimit (pullbackCone D p hp q hq g) := by
  have hsnd (s : Cone (pullbackDiagram D p hp g)) (i j : I) :
      s.π.app i ≫ pullback.snd _ _ = s.π.app j ≫ pullback.snd _ _ :=
    have : IsConnected I := IsCofiltered.isConnected I
    constant_of_preserves_morphisms (fun i ↦ s.π.app i ≫ pullback.snd (p i) g)
      (fun i j f ↦ by
        dsimp only
        rw [← s.w f, Category.assoc, pullbackDiagram_map, pullback.lift_snd,
          Category.comp_id]) i j
  let i₀ : I := (IsCofiltered.nonempty (C := I)).some
  let l (s : Cone (pullbackDiagram D p hp g)) : s.pt ⟶ c.pt :=
    hc.lift ⟨s.pt,
      { app i := s.π.app i ≫ pullback.fst _ _
        naturality i j f := by
          rw [Functor.const_obj_map]
          erw [Category.id_comp]
          rw [← s.w f, Category.assoc,
            Category.assoc, pullbackDiagram_map, pullback.lift_fst] }⟩
  have hl (s : Cone (pullbackDiagram D p hp g)) (i : I) :
      l s ≫ c.π.app i = s.π.app i ≫ pullback.fst _ _ := hc.fac _ i
  refine
    { lift s := pullback.lift (l s) (s.π.app i₀ ≫ pullback.snd _ _) (by
        rw [← hq i₀, ← Category.assoc, hl, Category.assoc, pullback.condition, Category.assoc])
      fac s i := by
        refine pullback.hom_ext ?_ ?_
        · simp [hl]
        · simp [hsnd s i₀ i]
      uniq s m hm := by
        refine pullback.hom_ext (hc.hom_ext fun i ↦ ?_) ?_
        · rw [pullback.lift_fst, hl, Category.assoc, ← hm i]
          simp
        · rw [pullback.lift_snd, ← hm i₀]
          simp }

/-- The transition maps of the base changed diagram are affine. -/
instance [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {i j : I} (f : i ⟶ j) :
    IsAffineHom ((pullbackDiagram D p hp g).map f) := by
  rw [pullbackDiagram_map]
  exact MorphismProperty.pullbackMap (P := @IsAffineHom) (inferInstanceAs (IsAffineHom _))
    (inferInstanceAs (IsAffineHom (𝟙 T))) (hp f).symm (Category.id_comp g).symm

end Pullback

section Pair

/-- The diagram `i ↦ Dᵢ ×_S Dᵢ`. -/
@[simps]
noncomputable abbrev pairDiagram : I ⥤ Scheme.{u} where
  obj i := pullback (p i) (p i)
  map {i j} f := pullback.map (p i) (p i) (p j) (p j) (D.map f) (D.map f) (𝟙 S) (by simp [hp])
    (by simp [hp])
  map_id i := by ext <;> simp
  map_comp f f' := by ext <;> simp

/-- The cone over the `Dᵢ ×_S Dᵢ` with point `lim Dᵢ ×_S lim Dᵢ`. -/
@[simps]
noncomputable abbrev pairCone : Cone (pairDiagram D p hp) where
  pt := pullback q q
  π :=
    { app i := pullback.map q q (p i) (p i) (c.π.app i) (c.π.app i) (𝟙 S) (by simp [hq])
        (by simp [hq])
      naturality i j f := by
        refine (Category.id_comp _).trans ?_
        ext <;> simp }

include hc hq in
/-- **Fibre products commute with cofiltered limits**:
`lim Dᵢ ×_S lim Dᵢ = lim (Dᵢ ×_S Dᵢ)`. -/
noncomputable def isLimitPairCone [IsCofiltered I] : IsLimit (pairCone D p hp q hq) := by
  let i₀ : I := (IsCofiltered.nonempty (C := I)).some
  let l₁ (s : Cone (pairDiagram D p hp)) : s.pt ⟶ c.pt :=
    hc.lift ⟨s.pt,
      { app i := s.π.app i ≫ pullback.fst _ _
        naturality i j f := by
          rw [Functor.const_obj_map]
          erw [Category.id_comp]
          rw [← s.w f, Category.assoc,
            Category.assoc, pairDiagram_map, pullback.lift_fst] }⟩
  let l₂ (s : Cone (pairDiagram D p hp)) : s.pt ⟶ c.pt :=
    hc.lift ⟨s.pt,
      { app i := s.π.app i ≫ pullback.snd _ _
        naturality i j f := by
          rw [Functor.const_obj_map]
          erw [Category.id_comp]
          rw [← s.w f, Category.assoc,
            Category.assoc, pairDiagram_map, pullback.lift_snd] }⟩
  have hl₁ (s : Cone (pairDiagram D p hp)) (i : I) :
      l₁ s ≫ c.π.app i = s.π.app i ≫ pullback.fst _ _ := hc.fac _ i
  have hl₂ (s : Cone (pairDiagram D p hp)) (i : I) :
      l₂ s ≫ c.π.app i = s.π.app i ≫ pullback.snd _ _ := hc.fac _ i
  refine
    { lift s := pullback.lift (l₁ s) (l₂ s) (by
        rw [← hq i₀, ← Category.assoc, hl₁, ← Category.assoc, hl₂, Category.assoc,
          pullback.condition, Category.assoc])
      fac s i := by
        refine pullback.hom_ext ?_ ?_
        · simp [hl₁]
        · simp [hl₂]
      uniq s m hm := by
        refine pullback.hom_ext (hc.hom_ext fun i ↦ ?_) (hc.hom_ext fun i ↦ ?_)
        · rw [pullback.lift_fst, hl₁, Category.assoc, ← hm i]
          simp
        · rw [pullback.lift_snd, hl₂, Category.assoc, ← hm i]
          simp }

/-- The transition maps of the base changed diagram are affine. -/
instance [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {i j : I} (f : i ⟶ j) :
    IsAffineHom ((pairDiagram D p hp).map f) := by
  rw [pairDiagram_map]
  exact MorphismProperty.pullbackMap (P := @IsAffineHom) (inferInstanceAs (IsAffineHom _))
    (inferInstanceAs (IsAffineHom _)) (hp f).symm (hp f).symm

end Pair

include hc hp hq in
/-- **A cofiltered limit of surjective affine `S`-schemes is surjective over `S`**: the fibre of
`lim Dᵢ` over a point `s ∈ S` is the limit of the fibres `Dᵢ ×_S Spec κ(s)`, which are nonempty
affine schemes, hence nonempty (Stacks Project Tag 01Z2). -/
theorem surjective_of_isLimit [IsCofiltered I] [∀ i, IsAffineHom (p i)]
    (hsurj : ∀ i, Function.Surjective (p i)) : Function.Surjective q := by
  intro s
  let g := S.fromSpecResidueField s
  have {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f) := by
    have : IsAffineHom (D.map f ≫ p j) := by rw [hp]; infer_instance
    exact IsAffineHom.of_comp _ (p j)
  have (i : I) : IsAffine ((pullbackDiagram D p hp g).obj i) := by
    rw [pullbackDiagram_obj]
    exact isAffine_of_isAffineHom (pullback.snd (p i) g)
  have (i : I) : Nonempty ((pullbackDiagram D p hp g).obj i) := by
    obtain ⟨x, hx⟩ := hsurj i s
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p i) (g := g) x
      (IsLocalRing.closedPoint _) (by rw [hx]; exact (S.fromSpecResidueField_apply s _).symm)
    exact ⟨z⟩
  obtain ⟨z⟩ := Scheme.nonempty_of_isLimit _ _ (isLimitPullbackCone D hc p hp q hq g)
  refine ⟨pullback.fst q g z, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact S.fromSpecResidueField_apply s _

/-- `Scheme.Hom.resLE` only depends on the morphism. -/
lemma resLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.resLE U V e = g.resLE U V e' := by
  subst h; rfl

include hc hp hq in
/-- **A cofiltered limit of affine étale `S`-schemes is weakly étale over `S`**: over an affine
open `U ⊆ S`, the preimage of `U` in `lim Dᵢ` is the limit of the affine étale `U`-schemes
`pᵢ⁻¹ U`, hence pro-(affine étale), hence weakly étale over `U`. -/
theorem weaklyEtale_of_isLimit [IsCofiltered I] [∀ i, IsAffineHom (p i)] [∀ i, Etale (p i)] :
    WeaklyEtale q := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f) := by
    have : IsAffineHom (D.map f ≫ p j) := by rw [hp]; infer_instance
    exact IsAffineHom.of_comp _ (p j)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @WeaklyEtale) _ (iSup_affineOpens_eq_top S)]
  intro U
  have : IsAffine U.1.toScheme := U.2
  refine proAffineEtale.weaklyEtale ?_
  obtain rfl := hq i₀
  let V := p i₀ ⁻¹ᵁ U.1
  have hle (j : Over i₀) : D.map j.hom ⁻¹ᵁ V ≤ p j.left ⁻¹ᵁ U.1 := by
    rw [← Scheme.Hom.comp_preimage, hp]
  refine ⟨Over i₀, inferInstance, inferInstance, opensDiagram D i₀ V,
    { app j := (p j.left).resLE U.1 _ (hle j)
      naturality j j' k := by
        simp only [opensDiagram_map, Functor.const_obj_map,
          Scheme.Hom.resLE_comp_resLE]
        exact resLE_congr (hp _) _ _ _ _ },
    (opensCone D c i₀ V).π, isLimitOpensCone D c hc i₀ V, fun j ↦ ⟨⟨?_, ?_, trivial⟩, ?_⟩⟩
  · dsimp; infer_instance
  · exact (U.2.preimage (p i₀)).preimage (D.map j.hom)
  · change (c.π.app j.left).resLE _ _ _ ≫ _ = _
    rw [Scheme.Hom.resLE_comp_resLE, ← Scheme.Hom.resLE_eq_morphismRestrict]
    exact resLE_congr (hq j.left) _ _ _ _


include hc in
/-- **A cofiltered limit of connected quasi-compact quasi-separated schemes with affine
transition maps is connected** (compare Stacks Project Tag 0CUF): an open and closed subset of
the limit and its complement are quasi-compact, hence preimages of quasi-compact opens of some
stage; at a later stage these are disjoint and cover (Stacks Project Tag 01Z4), so they are
open and closed in a connected scheme. -/
theorem connectedSpace_of_isLimit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, ConnectedSpace (D.obj i)] : ConnectedSpace c.pt := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : Nonempty c.pt := Scheme.nonempty_of_isLimit D c hc
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs ↦ ?_⟩
  let U : c.pt.Opens := ⟨s, hs.isOpen⟩
  let U' : c.pt.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  obtain ⟨i, V, hV, hVU⟩ := exists_preimage_eq D c hc U hs.isClosed.isCompact
  obtain ⟨j, V', hV', hVU'⟩ := exists_preimage_eq D c hc U' hs.isOpen.isClosed_compl.isCompact
  obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let A := D.map fki ⁻¹ᵁ V
  let B := D.map fkj ⁻¹ᵁ V'
  have hA : c.π.app k ⁻¹ᵁ A = U := by rw [← Scheme.Hom.comp_preimage, c.w, hVU]
  have hB : c.π.app k ⁻¹ᵁ B = U' := by rw [← Scheme.Hom.comp_preimage, c.w, hVU']
  have hAc : IsCompact (A : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V.2 hV
  have hBc : IsCompact (B : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V'.2 hV'
  obtain ⟨l, flk, hl⟩ := exists_map_preimage_eq_map_preimage D c hc (U := A ⊓ B) (V := ⊥)
    (QuasiSeparatedSpace.inter_isCompact _ _ A.2 hAc B.2 hBc) isCompact_empty (by
      rw [Scheme.Hom.preimage_inf, hA, hB, Scheme.Hom.preimage_bot]
      ext x
      simp [U, U'])
  obtain ⟨l', fl'k, hl'⟩ := exists_map_preimage_eq_map_preimage D c hc (U := A ⊔ B) (V := ⊤)
    (hAc.union hBc) isCompact_univ (by
      rw [Scheme.Hom.preimage_sup, hA, hB, Scheme.Hom.preimage_top]
      ext x
      simp [U, U'])
  obtain ⟨m, a, b, hab⟩ := IsCofiltered.cospan flk fl'k
  let W := D.map (a ≫ flk) ⁻¹ᵁ A
  let W' := D.map (a ≫ flk) ⁻¹ᵁ B
  have hinf : W ⊓ W' = ⊥ := by
    simp only [W, W', Functor.map_comp, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_inf, hl,
      Scheme.Hom.preimage_bot]
  have hsup : W ⊔ W' = ⊤ := by
    simp only [W, W', hab, Functor.map_comp, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_sup,
      hl', Scheme.Hom.preimage_top]
  have hW : IsClopen (W : Set (D.obj m)) := by
    refine ⟨⟨?_⟩, W.2⟩
    convert W'.2 using 1
    ext x
    have h1 := congrArg (x ∈ ·) hinf
    have h2 := congrArg (x ∈ ·) hsup
    simp only [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_sup, eq_iff_iff] at h1 h2
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    tauto
  have hsW : s = c.π.app m ⁻¹' W := by
    have : c.π.app m ⁻¹ᵁ W = U := by
      simp only [W, ← Scheme.Hom.comp_preimage, c.w, hA]
    change (U : Set c.pt) = _
    rw [← this]
    rfl
  rcases isClopen_iff.mp hW with h | h
  · left; rw [hsW, h, Set.preimage_empty]
  · right; rw [hsW, h, Set.preimage_univ]

end AlgebraicGeometry.Scheme
