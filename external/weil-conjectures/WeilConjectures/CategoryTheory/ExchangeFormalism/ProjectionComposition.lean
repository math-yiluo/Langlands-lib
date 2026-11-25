/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.CompositionCoherence
public import WeilConjectures.CategoryTheory.ExchangeFormalism.ProjectionExchange

/-!
# The exceptional projection morphisms and the composition isomorphisms

Let `F` be an exchange formalism whose categories are monoidal and whose pullbacks are monoidal,
compatibly with the composition isomorphisms. For a factorization `X ⟶[i] W ⟶[p] S` of `h` with
`i` an open immersion, the *exceptional projection morphism*
`PF_{i,p} : p_* i_! K ⊗ B ⟶ p_* i_! (K ⊗ h^* B)`
(`CategoryTheory.ExchangeFormalism.shriekProjection`) is the projection morphism of `p^* ⊣ p_*`,
followed by the inverse of the projection comparison of `i_! ⊣ i^*` and the identification
`i^* p^* ≅ h^*`.

The composition isomorphism of a triangle of factorizations intertwines these morphisms
(`CategoryTheory.ExchangeFormalism.compIso_hom_app_whiskerRight_comp_shriekProjection`): this is
the compatibility of the projection formula with the composition of compactly supported direct
images (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2). Its variant
`CategoryTheory.ExchangeFormalism.compIso_inv_app_whiskerRight_comp_of_eq` takes the exceptional
projection morphisms and the other data as variables subject to equations, so that it applies to
data spelled differently (for instance through the definitions of a concrete exchange formalism).

-/

@[expose] public section

universe w v₁ v u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪) [instMonoidal : ∀ X, MonoidalCategory (F.obj X)]
  [instMonoidalPb : ∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal]

/-- The exceptional projection morphism `PF_{i,p} : p_* i_! K ⊗ B ⟶ p_* i_! (K ⊗ h^* B)` of a
factorization `X ⟶[i] W ⟶[p] S` of `h`: the projection morphism of `p^* ⊣ p_*`, the inverse of the
projection comparison of `i_! ⊣ i^*` and the identification `i^* p^* ≅ h^*`. -/
noncomputable def shriekProjection {X W S : 𝒞} (i : X ⟶ W) [Fact (𝒪 i)] (p : W ⟶ S) (h : X ⟶ S)
    (w : i ≫ p = h) [∀ K N, IsIso ((F.shAdj i).projectionComparison K N)] (K : F.obj X)
    (B : F.obj S) :
    (F.shriek i p).obj K ⊗ B ⟶ (F.shriek i p).obj (K ⊗ (F.pb h).obj B) :=
  (F.adj p).projectionMorphism ((F.sh i).obj K) B ≫
    (F.pf p).map (inv ((F.shAdj i).projectionComparison K ((F.pb p).obj B)) ≫
      (F.sh i).map (K ◁ (F.pbComp' i p h w).inv.app B))

omit [∀ X, MonoidalCategory (F.obj X)] [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal] in
/-- **The pullback identifications of a triangle of factorizations agree**: for
`i₁ ≫ p₁ = f`, `i₂ ≫ p₂ = g`, `i₁ ≫ q = i`, `r ≫ p₂ = p` and `p₁ ≫ i₂ = q ≫ r`, the two
identifications `(f ≫ g)^* ≅ p₂^* ⋙ r^* ⋙ q^* ⋙ i₁^*`, through `i^* p^*` and through
`f^* g^*` and the square isomorphism, agree. -/
@[reassoc]
lemma pbComp'_hom_app_triangle {X Z₁ Y W Z₂ S : 𝒞} (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (i₂ : Y ⟶ Z₂) (p₂ : Z₂ ⟶ S) (q : Z₁ ⟶ W) (r : W ⟶ Z₂) (i : X ⟶ W) (p : W ⟶ S)
    (f : X ⟶ Y) (g : Y ⟶ S) (hf : i₁ ≫ p₁ = f) (hg : i₂ ≫ p₂ = g) (hi : i₁ ≫ q = i)
    (hp : r ≫ p₂ = p) (w : p₁ ≫ i₂ = q ≫ r) (hfg : i ≫ p = f ≫ g) (B : F.obj S) :
    (F.pbComp' i p (f ≫ g) hfg).hom.app B ≫ (F.pb i).map ((F.pbComp' r p₂ p hp).hom.app B) ≫
        (F.pbComp' i₁ q i hi).hom.app ((F.pb r).obj ((F.pb p₂).obj B)) =
      (F.pbComp f g).hom.app B ≫ (F.pbComp' i₁ p₁ f hf).hom.app ((F.pb g).obj B) ≫
        (F.pb i₁).map ((F.pb p₁).map ((F.pbComp' i₂ p₂ g hg).hom.app B) ≫
          (F.sqIso p₁ q i₂ r w).hom.app ((F.pb p₂).obj B)) := by
  have h₁ := F.pbComp'_assoc i r p₂ (i ≫ r) p (f ≫ g) rfl hp
    (by rw [Category.assoc, hp, hfg]) B
  have h₂ := F.pbComp'_assoc i₁ q r i (p₁ ≫ i₂) (i ≫ r) hi w.symm rfl ((F.pb p₂).obj B)
  have h₃ := F.pbComp'_assoc i₁ (p₁ ≫ i₂) p₂ (i ≫ r) (p₁ ≫ g) (f ≫ g)
    (by rw [← hi, w, Category.assoc]) (by rw [Category.assoc, hg])
    (by rw [Category.assoc, hp, hfg]) B
  have h₄ := F.pbComp'_assoc i₁ p₁ g f (p₁ ≫ g) (f ≫ g) hf rfl rfl B
  have h₅ := F.pbComp'_assoc p₁ i₂ p₂ (p₁ ≫ i₂) g (p₁ ≫ g) rfl hg (by rw [Category.assoc, hg]) B
  rw [pbComp'_rfl] at h₄
  rw [← reassoc_of% h₁, h₂, reassoc_of% h₃, reassoc_of% h₄, sqIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [← Functor.map_comp_assoc, ← h₅]
  simp

omit [∀ X, MonoidalCategory (F.obj X)] [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal] in
/-- The inverse form of `CategoryTheory.ExchangeFormalism.pbComp'_hom_app_triangle`. -/
lemma pbComp'_inv_app_triangle {X Z₁ Y W Z₂ S : 𝒞} (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (i₂ : Y ⟶ Z₂) (p₂ : Z₂ ⟶ S) (q : Z₁ ⟶ W) (r : W ⟶ Z₂) (i : X ⟶ W) (p : W ⟶ S)
    (f : X ⟶ Y) (g : Y ⟶ S) (hf : i₁ ≫ p₁ = f) (hg : i₂ ≫ p₂ = g) (hi : i₁ ≫ q = i)
    (hp : r ≫ p₂ = p) (w : p₁ ≫ i₂ = q ≫ r) (hfg : i ≫ p = f ≫ g) (B : F.obj S) :
    (F.pbComp' i₁ q i hi).inv.app ((F.pb r).obj ((F.pb p₂).obj B)) ≫
        (F.pb i).map ((F.pbComp' r p₂ p hp).inv.app B) ≫
        (F.pbComp' i p (f ≫ g) hfg).inv.app B ≫ (F.pbComp f g).hom.app B =
      (F.pb i₁).map ((F.sqIso p₁ q i₂ r w).inv.app ((F.pb p₂).obj B) ≫
          (F.pb p₁).map ((F.pbComp' i₂ p₂ g hg).inv.app B)) ≫
        (F.pbComp' i₁ p₁ f hf).inv.app ((F.pb g).obj B) := by
  rw [← cancel_epi ((F.pbComp' i p (f ≫ g) hfg).hom.app B ≫
    (F.pb i).map ((F.pbComp' r p₂ p hp).hom.app B) ≫
    (F.pbComp' i₁ q i hi).hom.app ((F.pb r).obj ((F.pb p₂).obj B)))]
  conv_rhs => rw [Category.assoc, Category.assoc,
    F.pbComp'_hom_app_triangle_assoc i₁ p₁ i₂ p₂ q r i p f g hf hg hi hp w hfg]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_comp,
    Functor.comp_obj, Category.comp_id]

/-- The flexible composition isomorphisms of the pullbacks are compatible with the
comultiplications of `h^*` and of the composite `g^* ⋙ f^*`, if the composition isomorphisms
are. -/
lemma δ_comp_pbComp'_hom_app_tensorHom
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (M N : F.obj Z) :
    δ (F.pb h) M N ≫ ((F.pbComp' f g h w).hom.app M ⊗ₘ (F.pbComp' f g h w).hom.app N) =
      (F.pbComp' f g h w).hom.app (M ⊗ N) ≫ δ (F.pb g ⋙ F.pb f) M N := by
  subst w
  rw [pbComp'_rfl, Functor.OplaxMonoidal.comp_δ]
  exact hδ f g M N

/-- **The projection morphism of a composite**: for `r ≫ p₂ = p`, the projection morphism of
`p^* ⊣ p_*` is that of `p₂^* ⊣ p₂_*` followed by `p₂_*` of that of `r^* ⊣ r_*`, through the
composition isomorphisms `p_* ≅ r_* ⋙ p₂_*` and `p^* ≅ p₂^* ⋙ r^*`. -/
lemma projectionMorphism_pfComp'
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    {W Z S : 𝒞} (r : W ⟶ Z) (p₂ : Z ⟶ S) (p : W ⟶ S) (hp : r ≫ p₂ = p) (M : F.obj W)
    (B : F.obj S) :
    (F.adj p).projectionMorphism M B =
      (F.pfComp' r p₂ p hp).hom.app M ▷ B ≫
        (F.adj p₂).projectionMorphism ((F.pf r).obj M) B ≫
        (F.pf p₂).map ((F.adj r).projectionMorphism M ((F.pb p₂).obj B)) ≫
        (F.pfComp' r p₂ p hp).inv.app _ ≫ (F.pf p).map (M ◁ (F.pbComp' r p₂ p hp).inv.app B) := by
  rw [Adjunction.projectionMorphism_eq_of_iso (F.adj p) ((F.adj p₂).comp (F.adj r))
    (F.pbComp' r p₂ p hp) (F.δ_comp_pbComp'_hom_app_tensorHom hδ r p₂ p hp) M B,
    Adjunction.projectionMorphism_comp]
  simp only [Category.assoc]
  rfl

/-- **The projection comparison of a composite open immersion**: for `i₁ ≫ q = i`, the
projection comparison of `i_! ⊣ i^*` is `q_!` of that of `i₁_! ⊣ i₁^*` followed by that of
`q_! ⊣ q^*`, through the composition isomorphisms `i_! ≅ i₁_! ⋙ q_!` and `i^* ≅ q^* ⋙ i₁^*`. -/
lemma projectionComparison_shComp'
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    {X Z₁ W : 𝒞} (i₁ : X ⟶ Z₁) (q : Z₁ ⟶ W) (i : X ⟶ W) [Fact (𝒪 i₁)] [Fact (𝒪 q)]
    [Fact (𝒪 i)] (hi : i₁ ≫ q = i) (K : F.obj X) (P : F.obj W) :
    (F.shAdj i).projectionComparison K P =
      (F.shComp' i₁ q i hi).hom.app (K ⊗ (F.pb i).obj P) ≫
        (F.sh q).map ((F.sh i₁).map (K ◁ (F.pbComp' i₁ q i hi).hom.app P)) ≫
        (F.sh q).map ((F.shAdj i₁).projectionComparison K ((F.pb q).obj P)) ≫
        (F.shAdj q).projectionComparison ((F.sh i₁).obj K) P ≫
        (F.shComp' i₁ q i hi).inv.app K ▷ P := by
  rw [Adjunction.projectionComparison_eq_of_iso_comp (F.shAdj i) (F.shAdj i₁) (F.shAdj q)
    (F.pbComp' i₁ q i hi) (F.δ_comp_pbComp'_hom_app_tensorHom hδ i₁ q i hi) K P]
  rfl

/-- The inverse of the projection comparison of a composite open immersion `i₁ ≫ q = i`, through
the composition isomorphisms (`CategoryTheory.ExchangeFormalism.projectionComparison_shComp'`). -/
lemma inv_projectionComparison_shComp'
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    [∀ {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] (K : F.obj X) (N : F.obj Y),
      IsIso ((F.shAdj j).projectionComparison K N)]
    {X Z₁ W : 𝒞} (i₁ : X ⟶ Z₁) (q : Z₁ ⟶ W) (i : X ⟶ W) [Fact (𝒪 i₁)] [Fact (𝒪 q)]
    [Fact (𝒪 i)] (hi : i₁ ≫ q = i) (K : F.obj X) (P : F.obj W) :
    inv ((F.shAdj i).projectionComparison K P) =
      (F.shComp' i₁ q i hi).hom.app K ▷ P ≫
        inv ((F.shAdj q).projectionComparison ((F.sh i₁).obj K) P) ≫
        (F.sh q).map (inv ((F.shAdj i₁).projectionComparison K ((F.pb q).obj P))) ≫
        (F.sh q).map ((F.sh i₁).map (K ◁ (F.pbComp' i₁ q i hi).inv.app P)) ≫
        (F.shComp' i₁ q i hi).inv.app (K ⊗ (F.pb i).obj P) := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [F.projectionComparison_shComp' hδ i₁ q i hi K P]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id_app, id_whiskerRight,
    Category.id_comp, IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Functor.comp_obj]
  rw [← Functor.map_comp, ← whiskerLeft_comp, Iso.hom_inv_id_app, whiskerLeft_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app]

/-- **The projection formulas of the open immersions of a triangle of factorizations**: on
`q_! i₁_! K ⊗ r^* p₂^* B`, the inverse projection comparison of `i = i₁ ≫ q` read through
`i_! ≅ i₁_! ⋙ q_!` and the identifications of the pullbacks is the inverse projection comparison
of `q` followed by `q_!` of that of `i₁`, read through the square isomorphism of
`p₁ ≫ i₂ = q ≫ r`. -/
lemma inv_projectionComparison_triangle
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    [∀ {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] (K : F.obj X) (N : F.obj Y),
      IsIso ((F.shAdj j).projectionComparison K N)]
    {X Z₁ Y W Z₂ S : 𝒞} (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (i₂ : Y ⟶ Z₂) (p₂ : Z₂ ⟶ S) (q : Z₁ ⟶ W) (r : W ⟶ Z₂) (i : X ⟶ W) (p : W ⟶ S)
    [Fact (𝒪 i₁)] [Fact (𝒪 q)] [Fact (𝒪 i)]
    (f : X ⟶ Y) (g : Y ⟶ S) (hf : i₁ ≫ p₁ = f) (hg : i₂ ≫ p₂ = g) (hi : i₁ ≫ q = i)
    (hp : r ≫ p₂ = p) (w : p₁ ≫ i₂ = q ≫ r) (hfg : i ≫ p = f ≫ g) (K : F.obj X)
    (B : F.obj S) :
    (F.shComp' i₁ q i hi).inv.app K ▷ (F.pb r).obj ((F.pb p₂).obj B) ≫
        (F.sh i).obj K ◁ (F.pbComp' r p₂ p hp).inv.app B ≫
        inv ((F.shAdj i).projectionComparison K ((F.pb p).obj B)) ≫
        (F.sh i).map (K ◁ (F.pbComp' i p (f ≫ g) hfg).inv.app B) ≫
        (F.sh i).map (K ◁ (F.pbComp f g).hom.app B) =
      inv ((F.shAdj q).projectionComparison ((F.sh i₁).obj K)
          ((F.pb r).obj ((F.pb p₂).obj B))) ≫
        (F.sh q).map ((F.sh i₁).obj K ◁ (F.sqIso p₁ q i₂ r w).inv.app ((F.pb p₂).obj B)) ≫
        (F.sh q).map ((F.sh i₁).obj K ◁ (F.pb p₁).map ((F.pbComp' i₂ p₂ g hg).inv.app B) ≫
          inv ((F.shAdj i₁).projectionComparison K ((F.pb p₁).obj ((F.pb g).obj B))) ≫
          (F.sh i₁).map (K ◁ (F.pbComp' i₁ p₁ f hf).inv.app ((F.pb g).obj B))) ≫
        (F.shComp' i₁ q i hi).inv.app (K ⊗ (F.pb f).obj ((F.pb g).obj B)) := by
  rw [(F.shAdj i).inv_projectionComparison_natural_right_assoc,
    F.inv_projectionComparison_shComp' hδ i₁ q i hi, Category.assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id_app, id_whiskerRight, Category.id_comp]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← whiskerLeft_comp, ← whiskerLeft_comp,
    ← (F.shComp' i₁ q i hi).inv.naturality, Functor.comp_map]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  rw [← whiskerLeft_comp_assoc, (F.shAdj i₁).inv_projectionComparison_natural_right_assoc,
    ← Functor.map_comp, ← Functor.map_comp, ← whiskerLeft_comp, ← whiskerLeft_comp,
    Functor.map_comp, Category.assoc,
    F.pbComp'_inv_app_triangle i₁ p₁ i₂ p₂ q r i p f g hf hg hi hp w hfg B, Functor.map_comp,
    Category.assoc]

/-- **The exchange map of a triangle of factorizations and the projection formulas**: the
exchange map `i₂_! p₁_* ⟶ r_* q_!` of the square `p₁ ≫ i₂ = q ≫ r`, followed by
`r_* q_! i₁_! ≅ r_* i_!`, carries the projection formula of `(i₂, p₁)` and that of `(i₁, p₁)`
to that of `(i, r)`, read through the identifications of the pullbacks. -/
lemma exchange_whiskerRight_comp_projectionMorphism_triangle
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    [∀ {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] (K : F.obj X) (N : F.obj Y),
      IsIso ((F.shAdj j).projectionComparison K N)]
    {X Z₁ Y W Z₂ S : 𝒞} (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (i₂ : Y ⟶ Z₂) (p₂ : Z₂ ⟶ S) (q : Z₁ ⟶ W) (r : W ⟶ Z₂) (i : X ⟶ W) (p : W ⟶ S)
    [Fact (𝒪 i₁)] [Fact (𝒪 i₂)] [Fact (𝒪 q)] [Fact (𝒪 i)]
    (f : X ⟶ Y) (g : Y ⟶ S) (hf : i₁ ≫ p₁ = f) (hg : i₂ ≫ p₂ = g) (hi : i₁ ≫ q = i)
    (hp : r ≫ p₂ = p) (w : p₁ ≫ i₂ = q ≫ r) (hfg : i ≫ p = f ≫ g)
    [IsIso (F.baseChange p₁ q i₂ r w)] (K : F.obj X) (B : F.obj S) :
    ((F.exchange p₁ q i₂ r w).app ((F.sh i₁).obj K) ≫
          (F.pf r).map ((F.shComp' i₁ q i hi).inv.app K)) ▷ (F.pb p₂).obj B ≫
        (F.adj r).projectionMorphism ((F.sh i).obj K) ((F.pb p₂).obj B) ≫
        (F.pf r).map ((F.sh i).obj K ◁ (F.pbComp' r p₂ p hp).inv.app B ≫
          (inv ((F.shAdj i).projectionComparison K ((F.pb p).obj B)) ≫
            (F.sh i).map (K ◁ (F.pbComp' i p (f ≫ g) hfg).inv.app B)) ≫
          (F.sh i).map (K ◁ (F.pbComp f g).hom.app B)) =
      (inv ((F.shAdj i₂).projectionComparison ((F.pf p₁).obj ((F.sh i₁).obj K))
          ((F.pb p₂).obj B)) ≫
          (F.sh i₂).map ((F.pf p₁).obj ((F.sh i₁).obj K) ◁ (F.pbComp' i₂ p₂ g hg).inv.app B)) ≫
        (F.sh i₂).map ((F.adj p₁).projectionMorphism ((F.sh i₁).obj K) ((F.pb g).obj B) ≫
          (F.pf p₁).map (inv ((F.shAdj i₁).projectionComparison K
              ((F.pb p₁).obj ((F.pb g).obj B))) ≫
            (F.sh i₁).map (K ◁ (F.pbComp' i₁ p₁ f hf).inv.app ((F.pb g).obj B)))) ≫
        (F.exchange p₁ q i₂ r w).app ((F.sh i₁).obj (K ⊗ (F.pb f).obj ((F.pb g).obj B))) ≫
        (F.pf r).map ((F.shComp' i₁ q i hi).inv.app (K ⊗ (F.pb f).obj ((F.pb g).obj B))) := by
  conv_rhs => rw [Category.assoc, ← Functor.map_comp_assoc,
    Adjunction.projectionMorphism_natural_right_assoc, ← Functor.map_comp, Functor.map_comp,
    Category.assoc, F.exchange_naturality_assoc,
    reassoc_of% (F.exchange_whiskerRight_comp_projectionMorphism hδ p₁ q i₂ r w
      ((F.sh i₁).obj K) ((F.pb p₂).obj B)).symm]
  rw [comp_whiskerRight, Category.assoc, Adjunction.projectionMorphism_natural_left_assoc]
  congr 2
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simpa only [Category.assoc, Functor.map_comp] using
    F.inv_projectionComparison_triangle hδ i₁ p₁ i₂ p₂ q r i p f g hf hg hi hp w hfg K B

/-- **The composition isomorphism intertwines the exceptional projection morphisms** (blueprint
`prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2): for a triangle of factorizations `T` of
`f : X ⟶ Y` and `g : Y ⟶ S`, through the composition isomorphism
`(i₁, p₁)_! ⋙ (i₂, p₂)_! ≅ (i, p)_!` and `(f ≫ g)^* ≅ g^* ⋙ f^*`, the exceptional projection
morphism of the composite factorization `(i, p)` of `f ≫ g` is that of `(i₂, p₂)` followed by
`(i₂, p₂)_!` of that of `(i₁, p₁)`. -/
theorem compIso_hom_app_whiskerRight_comp_shriekProjection
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    [∀ {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] (K : F.obj X) (N : F.obj Y),
      IsIso ((F.shAdj j).projectionComparison K N)]
    {X Y S : 𝒞} (T : ShriekTriangle 𝒪 X Y S)
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)]
    {f : X ⟶ Y} {g : Y ⟶ S} (hf : T.i₁ ≫ T.p₁ = f) (hg : T.i₂ ≫ T.p₂ = g)
    (hfg : T.i ≫ T.p = f ≫ g) (K : F.obj X) (B : F.obj S) :
    (F.compIso T).hom.app K ▷ B ≫ F.shriekProjection T.i T.p (f ≫ g) hfg K B ≫
        (F.shriek T.i T.p).map (K ◁ (F.pbComp f g).hom.app B) =
      F.shriekProjection T.i₂ T.p₂ g hg ((F.shriek T.i₁ T.p₁).obj K) B ≫
        (F.shriek T.i₂ T.p₂).map (F.shriekProjection T.i₁ T.p₁ f hf K ((F.pb g).obj B)) ≫
        (F.compIso T).hom.app (K ⊗ (F.pb f).obj ((F.pb g).obj B)) := by
  rw [compIso_hom_app, compIso_hom_app]
  dsimp only [shriekProjection, shriek, Functor.comp_obj, Functor.comp_map]
  rw [F.projectionMorphism_pfComp' hδ T.r T.p₂ T.p T.r_p]
  simp only [Category.assoc, comp_whiskerRight]
  rw [← comp_whiskerRight_assoc ((F.pfComp' T.r T.p₂ T.p T.r_p).inv.app _), Iso.inv_hom_id_app,
    id_whiskerRight, Category.id_comp, Adjunction.projectionMorphism_natural_left_assoc,
    ← Functor.map_comp, ← Functor.map_comp, ← (F.pfComp' T.r T.p₂ T.p T.r_p).inv.naturality,
    Functor.comp_map]
  simp only [← Functor.map_comp_assoc]
  congr 2
  exact congrArg (F.pf T.p₂).map (F.exchange_whiskerRight_comp_projectionMorphism_triangle hδ
    T.i₁ T.p₁ T.i₂ T.p₂ T.q T.r T.i T.p f g hf hg T.i_q T.r_p T.w hfg K B)

/-- `compIso_hom_app_whiskerRight_comp_shriekProjection` read through the inverse of the
composition isomorphism, with the exceptional projection morphisms, the composition isomorphism of
the pullbacks and the object `K ⊗ f^* g^* B` replaced by data equal to them, so that it applies to
data given in another form without unfolding it. -/
theorem compIso_inv_app_whiskerRight_comp_of_eq
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    [∀ {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] (K : F.obj X) (N : F.obj Y),
      IsIso ((F.shAdj j).projectionComparison K N)]
    {X Y S : 𝒞} (T : ShriekTriangle 𝒪 X Y S)
    [hbc : IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w)]
    [hex : IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)]
    {f : X ⟶ Y} {g : Y ⟶ S} (hf : T.i₁ ≫ T.p₁ = f) (hg : T.i₂ ≫ T.p₂ = g)
    (hfg : T.i ≫ T.p = f ≫ g) (K : F.obj X) (B : F.obj S) (W : F.obj X)
    (hW : K ⊗ (F.pb f).obj ((F.pb g).obj B) = W)
    (a : (F.shriek T.i T.p).obj K ⊗ B ⟶ (F.shriek T.i T.p).obj (K ⊗ (F.pb (f ≫ g)).obj B))
    (ha : a = F.shriekProjection T.i T.p (f ≫ g) hfg K B)
    (s : (F.pb (f ≫ g)).obj B ⟶ (F.pb g ⋙ F.pb f).obj B)
    (hs : s = (F.pbComp f g).hom.app B)
    (u : K ⊗ (F.pb (f ≫ g)).obj B ⟶ W) (hu : u = K ◁ s ≫ eqToHom hW)
    (t : (F.shriek T.i T.p).obj (K ⊗ (F.pb (f ≫ g)).obj B) ⟶ (F.shriek T.i T.p).obj W)
    (ht : t = (F.shriek T.i T.p).map u)
    (b : (F.shriek T.i₂ T.p₂).obj ((F.shriek T.i₁ T.p₁).obj K) ⊗ B ⟶
      (F.shriek T.i₂ T.p₂).obj ((F.shriek T.i₁ T.p₁).obj K ⊗ (F.pb g).obj B))
    (hb : b = F.shriekProjection T.i₂ T.p₂ g hg ((F.shriek T.i₁ T.p₁).obj K) B)
    (c : (F.shriek T.i₁ T.p₁).obj K ⊗ (F.pb g).obj B ⟶ (F.shriek T.i₁ T.p₁).obj W)
    (hc : c = F.shriekProjection T.i₁ T.p₁ f hf K ((F.pb g).obj B) ≫
      (F.shriek T.i₁ T.p₁).map (eqToHom hW)) :
    (F.compIso T).inv.app K ▷ B ≫ b ≫ (F.shriek T.i₂ T.p₂).map c ≫
        (F.compIso T).hom.app W = a ≫ t := by
  subst hW ha hs hu ht hb hc
  have h := F.compIso_hom_app_whiskerRight_comp_shriekProjection hδ T hf hg hfg K B
  simp only [eqToHom_refl, Category.comp_id, Functor.map_id]
  rw [← h, ← comp_whiskerRight_assoc, Iso.inv_hom_id_app, id_whiskerRight, Category.id_comp]

end CategoryTheory.ExchangeFormalism
