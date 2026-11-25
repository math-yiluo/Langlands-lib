/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-! # Reflection of equivariance through the inverse-image unit

Source: Stacks Project Tag 0A5G, final paragraph.
(blueprint: lem-weil-pbc-torsor-unit-equivariance-reflection)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A lifted map is equivariant if its transported map is equivariant.
Source: Stacks Project Tag 0A5G, final paragraph, action compatibility in the
finite étale interpretation of torsors.
(blueprint: lem-weil-pbc-torsor-unit-equivariance-reflection)

Proof: For each m in M, the constant section defines natural translation
endomorphisms a₁(m) and a₂(m) of the two original torsor sheaves. Naturality
of the inverse-image unit and its displayed compatibility with e₁ and e₂
show, on every section over every W, that the adjoints of
L(a₁(m) ≫ f) ≫ e₂.hom and L(f ≫ a₂(m)) ≫ e₂.hom are equal:
use compatibility for e₁, equivariance of φ, then compatibility for e₂.
The adjunction bijection and cancellation of e₂.hom give equality of the
inverse images. Injectivity of L.map on this Hom set gives
 a₁(m) ≫ f = f ≫ a₂(m). Finally the sheafification map from the constant presheaf M is locally
surjective. Its image sieve on any coefficient section is covering.
On each arrow in that sieve the section is the image of some m in M.
Naturality of f and both actions reduces the desired equation there to
the constant-section equation just proved; separatedness of T₂ glues them.
No injectivity of individual unit components, no points of the base,
and no surjectivity of i are used. -/
theorem torsor_map_equivariant_of_unit
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (M : Type (u + 1)) [AddCommGroup M]
    (T₁ T₂ : Sheaf.Torsor
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)))
    (R₁ R₂ : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (e₁ : (Scheme.etaleSetPullback i).obj T₁.sheaf ≅ R₁.sheaf)
    (e₂ : (Scheme.etaleSetPullback i).obj T₂.sheaf ≅ R₂.sheaf)
    (he₁ :
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T₁.sheaf.obj.obj (op W)),
      e₁.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T₁.sheaf).hom.app (op W)
            (T₁.vadd (op W) g t)) =
      R₁.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (e₁.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T₁.sheaf).hom.app (op W) t))))
    (he₂ :
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T₂.sheaf.obj.obj (op W)),
      e₂.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T₂.sheaf).hom.app (op W)
            (T₂.vadd (op W) g t)) =
      R₂.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (e₂.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T₂.sheaf).hom.app (op W) t))))
    (f : T₁.sheaf ⟶ T₂.sheaf)
    (hinj : Function.Injective
      (fun k : T₁.sheaf ⟶ T₂.sheaf ↦ (Scheme.etaleSetPullback i).map k))
    (φ : R₁.sheaf ⟶ R₂.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (R₁.vadd U g t) =
      R₂.vadd U g (φ.hom.app U t))
    (hf : (Scheme.etaleSetPullback i).map f ≫ e₂.hom = e₁.hom ≫ φ) :
    ∀ U g t, f.hom.app U (T₁.vadd U g t) = T₂.vadd U g (f.hom.app U t) := by
  let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  let η := toSheafify Y.smallEtaleTopology
    ((Functor.const Y.Etaleᵒᵖ).obj (AddCommGrpCat.of M))
  let c (U : Y.Etaleᵒᵖ) (m : M) : G.obj.obj U := η.app U m
  have hc {U V : Y.Etaleᵒᵖ} (k : U ⟶ V) (m : M) :
      G.obj.map k (c U m) = c V m := by
    exact (NatTrans.naturality_apply η k m).symm
  let a (T : Sheaf.Torsor G) (m : M) : T.sheaf ⟶ T.sheaf :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (T.vadd U (c U m))
       naturality := fun U V k ↦ by
         ext t
         change T.vadd V (c V m) (T.sheaf.obj.map k t) =
           T.sheaf.obj.map k (T.vadd U (c U m) t)
         rw [T.map_vadd, hc] }⟩
  have ha (m : M) : a T₁ m ≫ f = f ≫ a T₂ m := by
    apply hinj
    let L := Scheme.etaleSetPullback i
    let D := (MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous
      (Type (u + 1)) (Y.smallGrothendieckTopology @Etale)
      (Y₀.smallGrothendieckTopology @Etale)
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
      (Y.smallGrothendieckTopology @Etale) (Y₀.smallGrothendieckTopology @Etale)
    apply (cancel_mono e₂.hom).mp
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, ← Category.assoc]
    change ((adj.unit.app T₁.sheaf ≫ D.map (L.map (a T₁ m))) ≫
      D.map (L.map f)) ≫ D.map e₂.hom =
      ((adj.unit.app T₁.sheaf ≫ D.map (L.map f)) ≫
      D.map (L.map (a T₂ m))) ≫ D.map e₂.hom
    have hn₁ := adj.unit.naturality (a T₁ m)
    have hn₂ := adj.unit.naturality f
    change a T₁ m ≫ adj.unit.app T₁.sheaf =
      adj.unit.app T₁.sheaf ≫ D.map (L.map (a T₁ m)) at hn₁
    change f ≫ adj.unit.app T₂.sheaf =
      adj.unit.app T₁.sheaf ≫ D.map (L.map f) at hn₂
    rw [← hn₁, ← hn₂]
    have hn₃ := adj.unit.naturality (a T₂ m)
    change a T₂ m ≫ adj.unit.app T₂.sheaf =
      adj.unit.app T₂.sheaf ≫ D.map (L.map (a T₂ m)) at hn₃
    have hD := congr_arg D.map hf
    change D.map (L.map f ≫ e₂.hom) = D.map (e₁.hom ≫ φ) at hD
    simp only [D.map_comp] at hD
    have hs : f ≫ adj.unit.app T₂.sheaf ≫ D.map e₂.hom =
        adj.unit.app T₁.sheaf ≫ D.map e₁.hom ≫ D.map φ := by
      rw [← Category.assoc, hn₂, Category.assoc, hD]
    have hn₃' := congr_arg (fun q ↦ q ≫ D.map e₂.hom) hn₃
    simp only [Category.assoc] at hn₃'
    simp only [Category.assoc]
    rw [hD, ← hn₃']
    ext W t
    change φ.hom.app _ (e₁.hom.hom.app _
      ((adj.unit.app T₁.sheaf).hom.app W (T₁.vadd W (c W m) t))) =
      e₂.hom.hom.app _ ((adj.unit.app T₂.sheaf).hom.app W
        (T₂.vadd W (c W m) (f.hom.app W t)))
    let W₀ := (MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W
    let b := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
      G).hom.app W (c W m)
    have he₁' := he₁ W.unop (c W m) t
    have he₂' := he₂ W.unop (c W m) (f.hom.app W t)
    change e₁.hom.hom.app W₀ ((adj.unit.app T₁.sheaf).hom.app W
      (T₁.vadd W (c W m) t)) = R₁.vadd W₀ b
      (e₁.hom.hom.app W₀ ((adj.unit.app T₁.sheaf).hom.app W t)) at he₁'
    change e₂.hom.hom.app W₀ ((adj.unit.app T₂.sheaf).hom.app W
      (T₂.vadd W (c W m) (f.hom.app W t))) = R₂.vadd W₀ b
      (e₂.hom.hom.app W₀ ((adj.unit.app T₂.sheaf).hom.app W
        (f.hom.app W t))) at he₂'
    rw [he₁', hφ, he₂']
    congr 1
    exact (congr_arg (fun q : T₁.sheaf ⟶ D.obj R₂.sheaf ↦
      q.hom.app W t) hs).symm
  intro U g t
  have hcover := Presheaf.imageSieve_mem Y.smallEtaleTopology η g
  apply ((isSheaf_iff_isSheaf_of_type Y.smallEtaleTopology T₂.sheaf.obj).1
    T₂.sheaf.property _ hcover).isSeparatedFor.ext
  intro V k hk
  obtain ⟨m, hm⟩ := hk
  change c (op V) m = G.obj.map k.op g at hm
  rw [← NatTrans.naturality_apply f.hom, T₁.map_vadd, T₂.map_vadd]
  change f.hom.app (op V) (T₁.vadd (op V) (G.obj.map k.op g)
    (T₁.sheaf.obj.map k.op t)) = T₂.vadd (op V) (G.obj.map k.op g)
    (T₂.sheaf.obj.map k.op (f.hom.app U t))
  rw [← hm, ← NatTrans.naturality_apply f.hom]
  exact congr_arg (fun q : T₁.sheaf ⟶ T₂.sheaf ↦
    q.hom.app (op V) (T₁.sheaf.obj.map k.op t)) (ha m)

end AlgebraicGeometry.Etale
