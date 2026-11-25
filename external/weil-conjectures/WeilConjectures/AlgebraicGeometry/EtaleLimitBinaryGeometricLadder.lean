/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.AlgebraicGeometry.StageCohomologyComparison
import WeilConjectures.AlgebraicGeometry.EtaleLimitBinaryZeroRestrictionRow
import WeilConjectures.AlgebraicGeometry.EtaleLimitBinarySuccessorCoconeSegment
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Connected
/-! # Geometric Mayer--Vietoris ladder before continuity

Source: Stacks Project, Tags 09YQ and 0A50.
(blueprint: lem-weil-pbc-etale-limit-binary-geometric-ladder).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem exact_zero_of_injective
    {A B C : AddCommGrpCat.{u + 1}} (f : B ⟶ C) (hf : Function.Injective f) :
    Function.Exact (0 : A ⟶ B) f := by
  intro x
  constructor
  · intro hx
    have hx0 : x = 0 := hf (hx.trans (map_zero f.hom).symm)
    exact ⟨0, by simpa using hx0.symm⟩
  · rintro ⟨y, rfl⟩
    simp

private theorem exact_into_subsingleton
    {A B C : AddCommGrpCat.{u + 1}} [Subsingleton B] :
    Function.Exact (0 : A ⟶ B) (0 : B ⟶ C) := by
  intro x
  constructor
  · intro _
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro _
    simp

private theorem colimit_square
    {J : Type u} [Category J] {K₁ K₂ : J ⥤ AddCommGrpCat.{u + 1}}
    (a : K₁ ⟶ K₂) (C₁ : Cocone K₁) (C₂ : Cocone K₂)
    (a' : C₁.pt ⟶ C₂.pt)
    (h : ∀ j, a.app j ≫ C₂.ι.app j = C₁.ι.app j ≫ a') :
    colimMap a ≫ colimit.desc K₂ C₂ = colimit.desc K₁ C₁ ≫ a' := by
  apply colimit.hom_ext
  intro j
  simpa only [Category.assoc, ι_colimMap_assoc, colimit.ι_desc,
    colimit.ι_desc_assoc] using h j

private theorem cofinal_middle_square
    {I J : Type u} [Category I] [Category J]
    (t : J ⥤ I) [t.Final] (H : I ⥤ AddCommGrpCat.{u + 1})
    {K : J ⥤ AddCommGrpCat.{u + 1}} (b : K ⟶ t ⋙ H)
    (C : Cocone K) (B : Cocone H) (b' : C.pt ⟶ B.pt)
    (h : ∀ j, b.app j ≫ B.ι.app (t.obj j) = C.ι.app j ≫ b') :
    colimMap b ≫ (Functor.Final.colimitIso t H).hom ≫ colimit.desc H B =
      colimit.desc K C ≫ b' := by
  apply colimit.hom_ext
  intro j
  simpa only [Category.assoc, ι_colimMap_assoc,
    Functor.Final.ι_colimitIso_hom_assoc, colimit.ι_desc,
    colimit.ι_desc_assoc] using h j

private theorem cofinal_right_square
    {I J : Type u} [Category I] [Category J]
    (t : J ⥤ I) [t.Final] (H : I ⥤ AddCommGrpCat.{u + 1})
    {K : J ⥤ AddCommGrpCat.{u + 1}} (r : t ⋙ H ⟶ K)
    (B : Cocone H) {B₄ : AddCommGrpCat.{u + 1}}
    (v₄ : colimit K ⟶ B₄) (r' : B.pt ⟶ B₄)
    (h : ∀ j, r.app j ≫ colimit.ι K j ≫ v₄ = B.ι.app (t.obj j) ≫ r') :
    (Functor.Final.colimitIso t H).inv ≫ colimMap r ≫ v₄ =
      colimit.desc H B ≫ r' := by
  have hs : colimMap r ≫ v₄ =
      (Functor.Final.colimitIso t H).hom ≫ colimit.desc H B ≫ r' := by
    apply colimit.hom_ext
    intro j
    simpa only [Category.assoc, ι_colimMap_assoc,
      Functor.Final.ι_colimitIso_hom_assoc, colimit.ι_desc_assoc] using h j
  rw [hs, Iso.inv_hom_id_assoc]

/-- Exact natural ladder with certified neighboring comparisons, without assuming continuity.

Source: Stacks Project, Tag 09YQ (theorem-colimit), restriction of its coherent systems,
and Tag 0A50 (lemma-mayer-vietoris), its exact sequence and coefficient naturality.
(blueprint: lem-weil-pbc-etale-limit-binary-geometric-ladder).

Proof: Pass to the cofinal directed tail above i₀ and transfer U and V to the
union stage by e. Restrict the scheme diagram and cone to inverse-image opens.
The restricted cones are limits by isLimitOpensCone. Affine projections and
transitions preserve compactness of the opens; opens inherit quasi-separatedness.
The intersection is compact on the quasi-separated union stage, without assuming
that the ambient X is quasi-separated. Restrict the coherent coefficients by
inverse image. Its identity and composition isomorphisms give coherence, and its
left adjoint property preserves the sheaf colimit. Construct the canonical
cohomology diagrams and cocones in every degree, using pullback functoriality.
Each has a stage isomorphic to U, V or their intersection. Their comparisons
therefore have system certificates; no continuity has been applied.

For p=q+1 use the Mayer--Vietoris segment whose first two terms are the degree-q
product on U,V and the degree-q group on their intersection, and whose fourth
term is the degree-p product. Keep these as functors K₁,K₂,K₃,K₄ on the directed tail, with
Mayer--Vietoris maps as natural transformations. Their two pairs are pointwise exact.
Finality supplies eQ from the tail middle colimit to the original middle colimit.
Filtered colimits commute with finite products for the neighboring comparisons.
The limit Mayer--Vietoris segment has the actual restriction r' of the statement.
Pullback naturality and coefficient naturality of the connecting map and of the
restrictions give the three squares, including the middle comparison prescribed
by hB. The three neighboring comparisons are products of system comparisons,
or one system comparison, conjugated by the cofinality and coefficient isomorphisms.
Use the iso, comp and prod certificate constructors for these conjugations.

For p=0 take K₁,K₂ to be constant zero functors and B₁,B₂ to be zero groups.
Their comparisons are isomorphisms, so use iso certificates. Take K₃ to be the
tail middle diagram and K₄ the degree-zero stage products on U,V.
Initial restriction injectivity in Mayer--Vietoris
gives pointwise Exact b r; the other exact pairs and first two squares are automatic.
The last square is restriction naturality, and its comparison has a product
certificate as above. No negative-degree term is used.

Empty and coincident opens give the same constructions, with zero factors or
diagonal and difference maps. All objects are eliminated only inside this proof;
no definition chooses data from the existential connecting-map assertions.
This lemma supplies geometry and stage exactness. It asserts neither exactness
of the two colimit pairs nor surjectivity or injectivity of the neighboring comparisons. -/
theorem etale_limit_binary_geometric_ladder
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p))
    (i₀ : I) (e : D.obj (op i₀) ≅ (U ⊔ V).toScheme) :
    let WU := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ e.hom ≫ (U ⊔ V).ι) ⁻¹ᵁ V
    let B₄ := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) p ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) p)
    let r' : B.pt ⟶ B₄ := AddCommGrpCat.ofHom
      (((cohomologyMap WU.ι L.pt p).prod (cohomologyMap WV.ι L.pt p)).comp eB.hom.hom)
    ∃ (J : Type u) (order : Preorder J),
      letI := order
      ∃ (directed : IsDirected J (· ≤ ·)) (nonempty : Nonempty J),
      letI := directed
      letI := nonempty
      ∃ (K₁ K₂ K₃ K₄ : J ⥤ AddCommGrpCat.{u + 1})
        (a : K₁ ⟶ K₂) (b : K₂ ⟶ K₃) (r : K₃ ⟶ K₄)
        (eQ : colimit K₃ ≅ colimit H)
        (B₁ B₂ : AddCommGrpCat.{u + 1})
        (a' : B₁ ⟶ B₂) (b' : B₂ ⟶ B.pt)
        (v₁ : colimit K₁ ⟶ B₁) (v₂ : colimit K₂ ⟶ B₂)
        (v₄ : colimit K₄ ⟶ B₄),
        (∀ j, Function.Exact (a.app j) (b.app j)) ∧
        (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₁ ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₂ ∧
        StageCohomologyComparison
          (fun S => S = U.toScheme ∨ S = V.toScheme ∨ S = (U ⊓ V).toScheme) v₄ ∧
        (∀ x, v₂ (colimMap a x) = a' (v₁ x)) ∧
        (∀ x, (colimit.desc H B) ((colimMap b ≫ eQ.hom) x) = b' (v₂ x)) ∧
        (∀ x, v₄ ((eQ.inv ≫ colimMap r) x) = r' ((colimit.desc H B) x)) := by
  classical
  cases p with
  | zero =>
    obtain ⟨J, order, directed, nonempty, t, ht, K₄, r, v₄, hr, hv₄, hright⟩ :=
      etale_limit_binary_zero_restriction_row X U V hU hV D c hc F φ hidentity
        hcomposition G eG hG L hL H eH hH B eB hB i₀ e
    let := order
    let := directed
    let := nonempty
    let := ht
    let : IsFiltered J := isFiltered_of_directed_le_nonempty J
    let : IsConnected J := IsFiltered.isConnected J
    let Z : J ⥤ AddCommGrpCat.{u + 1} :=
      (Functor.const J).obj (AddCommGrpCat.of PUnit.{u + 2})
    let eZ : @colimit J _ (AddCommGrpCat.{u + 1}) _ Z _ ≅
        AddCommGrpCat.of PUnit.{u + 2} :=
      (colimit.isColimit Z).coconePointUniqueUpToIso (isColimitConstCocone J _)
    let : Subsingleton (@colimit J _ (AddCommGrpCat.{u + 1}) _ Z _) :=
      (Equiv.subsingleton_congr eZ.addCommGroupIsoToAddEquiv.toEquiv).mpr inferInstance
    let : ∀ j, Subsingleton (Z.obj j) := by
      intro j
      change Subsingleton PUnit
      infer_instance
    refine ⟨J, order, directed, nonempty, Z, Z, t ⋙ H, K₄, 0, 0, r,
      Functor.Final.colimitIso t H, colimit Z, colimit Z, 0, 0, 𝟙 _, 𝟙 _, v₄,
      ?_, ?_, ?_, ?_, ?_, hv₄, ?_, ?_, ?_⟩
    · intro j
      exact exact_into_subsingleton
    · intro j
      exact exact_zero_of_injective (r.app j) (hr j)
    · exact exact_into_subsingleton
    · exact StageCohomologyComparison.iso (Iso.refl _)
    · exact StageCohomologyComparison.iso (Iso.refl _)
    · intro x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    · intro x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    · intro x
      exact congrArg (fun f => f x) (cofinal_right_square t H r B v₄ _ hright)
  | succ q =>
    obtain ⟨J, order, directed, nonempty, t, ht, K₁, K₂, K₄, a, b, r,
      C₁, C₂, a', b', v₄, hab, hbr, hab', hv₁, hv₂, hv₄, ha, hb, hr⟩ :=
      etale_limit_binary_successor_cocone_segment X U V hU hV D c hc F φ hidentity
        hcomposition G eG hG L hL q H eH hH B eB hB i₀ e
    let := order
    let := directed
    let := nonempty
    let := ht
    refine ⟨J, order, directed, nonempty, K₁, K₂, t ⋙ H, K₄, a, b, r,
      Functor.Final.colimitIso t H, C₁.pt, C₂.pt, a', b', colimit.desc K₁ C₁,
      colimit.desc K₂ C₂, v₄, hab, hbr, hab', hv₁, hv₂, hv₄, ?_, ?_, ?_⟩
    · intro x
      exact congrArg (fun f => f x) (colimit_square a C₁ C₂ a' ha)
    · intro x
      exact congrArg (fun f => f x) (cofinal_middle_square t H b C₂ B b' hb)
    · intro x
      exact congrArg (fun f => f x) (cofinal_right_square t H r B v₄ _ hr)


end AlgebraicGeometry.Etale
