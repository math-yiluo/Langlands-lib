/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineStageTailColimit
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Finite-stage vanishing when one stage is affine

Source: Stacks Project, Tag 09YQ (theorem-colimit), cofinal-tail reduction.
(blueprint: lem-weil-pbc-etale-limit-affine-stage-eventual-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A class whose comparison image is zero vanishes at a later stage.

Source: Stacks Project, Tag 09YQ (theorem-colimit); the cofinal-tail argument of
lem-weil-pbc-etale-limit-cohomology-affine-stage, followed by finite-stage equality
in a filtered colimit of abelian groups.
(blueprint: lem-weil-pbc-etale-limit-affine-stage-eventual-zero).

Proof: fix a class x at i mapping to zero. Restrict the entire supplied system to
indices j above i0. Directedness makes this tail nonempty, directed and final;
its opposite is initial. The whiskered scheme cone remains a limit, and the
whiskered sheaf cocone remains a colimit. Every tail scheme is affine because its
map to D_i0 is affine. Restrict F, phi, eG and eH and all their identity,
composition, transition and leg equations along the inclusion. Apply affine
comparison (Tag 09YQ, via affine-site continuity Tags 0EYL and 09YP): the
restricted B is a colimit. Finality then makes the original B a colimit.
For an index i outside the tail, first move x to a common upper bound of i and
i0. Naturality of B makes its comparison image zero there; compose the eventual
vanishing transition with i's transition to that upper bound.
The forgetful functor from abelian groups preserves filtered colimits. In that
filtered colimit, x and zero at i have equal images by hypothesis. The equality
criterion for a filtered colimit gives j and f : i to j with H.map f x =
H.map f 0 = 0. This proves only kernel detection, not class descent or the
colimit universal property. For x = 0 choose the identity. Degree zero is the
same equality argument; zero sheaves, empty affine schemes and singleton index
systems need no exceptions. Earlier schemes need not be affine. -/
/- Tail lemma for the affine cofinal subsystem.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail)

Proof: apply the affine-stage eventual-zero theorem to the tail subsystem. -/
theorem etale_limit_affine_stage_eventual_zero_tail
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
    (i₀ : I) [IsAffine (D.obj (op i₀))] :
    ∀ (i : I) (_hi : i₀ ≤ i) (x : H.obj i), (B.ι.app i).hom x = 0 →
      ∃ (j : I) (f : i ⟶ j), (H.map f).hom x = 0  := by
  intro i hi x hx
  let J := Set.Ici i₀
  let t : J ⥤ I := (Subtype.mono_coe (· ∈ Set.Ici i₀)).functor
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨hBT⟩ := etale_limit_affine_stage_tail_colimit
    D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB i₀
  let it : J := ⟨i, hi⟩
  have hx0 : ((B.whisker t).ι.app it) x = ((B.whisker t).ι.app it) (0 : H.obj i) := by
    change (B.ι.app i).hom x = (B.ι.app i).hom 0
    rw [hx, map_zero]
  obtain ⟨j, f, hf⟩ := (hBT.eq_iff' (i := it) x (0 : (t ⋙ H).obj it)).mp hx0
  refine ⟨t.obj j, t.map f, ?_⟩
  change (H.map (t.map f)).hom x = (H.map (t.map f)).hom 0 at hf
  rw [map_zero] at hf
  exact hf

/-- (blueprint: lem-weil-pbc-etale-limit-affine-stage-eventual-zero) -/
theorem etale_limit_affine_stage_eventual_zero
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
    (i₀ : I) [IsAffine (D.obj (op i₀))] :
    ∀ (i : I) (x : H.obj i), (B.ι.app i).hom x = 0 →
      ∃ (j : I) (f : i ⟶ j), (H.map f).hom x = 0  := by
  intro i x hx
  obtain ⟨j, hij, hj⟩ := exists_ge_ge i i₀
  obtain ⟨k, g, hg⟩ := etale_limit_affine_stage_eventual_zero_tail
    D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB i₀ j hj
    (H.map (homOfLE hij) x) (by
    change (H.map (homOfLE hij) ≫ B.ι.app j) x = 0
    rw [B.w]
    exact hx)
  refine ⟨k, homOfLE hij ≫ g, ?_⟩
  rw [H.map_comp]
  exact hg

end AlgebraicGeometry.Etale
