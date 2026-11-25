/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Sites.LocalSite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantStalk

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def etale_identity_isTerminal (S : Scheme.{u}) :
    IsTerminal (Etale.mk (𝟙 S)) :=
  MorphismProperty.Over.mkIdTerminal @Etale S

private theorem spec_algClosed_etale_localSite
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (Spec (CommRingCat.of Ω)).smallEtaleTopology.IsLocalSite where
  eq_top_of_mem R hR := by
    let S := Spec (CommRingCat.of Ω)
    let Φ := pointSmallEtale (𝟙 S)
    let I := Etale.mk (𝟙 S)
    have hI : IsTerminal I := etale_identity_isTerminal S
    let T := ⊤_ S.Etale
    let xI : Φ.fiber.obj I := Over.homMk (𝟙 _) (Category.comp_id _)
    let xT := Φ.fiber.map (terminal.from I) xI
    obtain ⟨Y, f, hf, y, _⟩ := Φ.jointly_surjective R hR xT
    let g : T ⟶ Y := hI.from T ≫ MorphismProperty.Over.homMk y.left y.w
    have hgf : g ≫ f = 𝟙 T := terminalIsTerminal.hom_ext _ _
    apply Sieve.id_mem_iff_eq_top.mp
    simpa only [hgf] using R.downward_closed hf g

private theorem spec_algClosed_etale_iso_of_terminal
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {F G : Sheaf (Spec (CommRingCat.of Ω)).smallEtaleTopology (Type (u + 1))}
    (f : F ⟶ G)
    [IsIso (f.hom.app (Opposite.op (⊤_ (Spec (CommRingCat.of Ω)).Etale)))] :
    IsIso f := by
  let S := Spec (CommRingCat.of Ω)
  let Φ := pointSmallEtale (𝟙 S)
  let I := Etale.mk (𝟙 S)
  let xI : Φ.fiber.obj I := Over.homMk (𝟙 _) (Category.comp_id _)
  have : IsIso (f.hom.app (Opposite.op I)) := by
    let e := (etale_identity_isTerminal S).uniqueUpToIso terminalIsTerminal
    exact (NatTrans.isIso_app_iff_of_iso f.hom e.op).1 inferInstance
  have hF : IsIso (Φ.toPresheafFiber I xI F.obj) :=
    (isIso_iff_bijective _).2 (spec_algClosed_etale_sheaf_constant_stalk Ω F)
  have hG : IsIso (Φ.toPresheafFiber I xI G.obj) :=
    (isIso_iff_bijective _).2 (spec_algClosed_etale_sheaf_constant_stalk Ω G)
  have hΦ : IsIso (Φ.sheafFiber.map f) := by
    change IsIso (Φ.presheafFiber.map f.hom)
    have h := Φ.toPresheafFiber_naturality f.hom I xI
    have : IsIso (Φ.toPresheafFiber I xI F.obj ≫ Φ.presheafFiber.map f.hom) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (Φ.toPresheafFiber I xI F.obj) _
  have hs : ⋃ _ : PUnit.{u + 1}, Set.range (𝟙 S) = Set.univ := by
    ext x
    simp
  have hc := isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ S
    (fun _ : PUnit.{u + 1} ↦ 𝟙 S) hs
  apply (hc.jointlyReflectIsomorphisms_type.isIso_iff f).2
  rintro ⟨-, ⟨i⟩⟩
  let e := Φ.uliftSheafFiberIso.{u + 1} (Type (u + 1))
  have he := e.hom.naturality f
  have : IsIso ((Φ.ulift.{u + 1}).sheafFiber.map f ≫ e.hom.app G) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app G)

/-- The constant-sheaf counit is an isomorphism in the algebraically closed étale case.
Source: Stacks Project, Remark 59.23.2 (Tag 03P5).
(blueprint: lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant-counit).

Proof: An etale scheme over Ω is the disjoint union of its open singleton points,
by the discrete separable fibre theorem. Each residue extension is finite separable
and hence equals Ω, so each singleton is a copy of Spec Ω over the base. The sheaf
condition for this covering identifies G(U) with the product of G(Spec Ω), since
distinct singletons have empty intersections and a sheaf has one section on the
empty object. The constant sheaf with value G(Spec Ω) has the same product of
sections: its sections on each singleton are its value, by the connected constant
sheaf comparison. On each singleton the adjunction counit is the identity of that
value. Consequently its map on U is a product of bijections, including the empty
product, and thus a bijection. Componentwise bijectivity gives an isomorphism of
presheaves and hence of sheaves. -/
theorem spec_algClosed_etale_sheaf_constant_counit
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf ((Spec (CommRingCat.of Ω)).smallEtaleTopology) (Type (u + 1))) :
    IsIso ((constantSheafAdj (Spec (CommRingCat.of Ω)).smallEtaleTopology
      (Type (u + 1)) terminalIsTerminal).counit.app G) := by
  let S := Spec (CommRingCat.of Ω)
  let J := S.smallEtaleTopology
  have : J.IsLocalSite := spec_algClosed_etale_localSite Ω
  let R := (sheafSections J (Type (u + 1))).obj (Opposite.op (⊤_ S.Etale))
  let adj := constantSheafAdj J (Type (u + 1)) terminalIsTerminal
  have : IsIso (adj.unit.app (R.obj G)) := inferInstance
  have h := adj.right_triangle_components G
  have : IsIso (adj.unit.app (R.obj G) ≫ R.map (adj.counit.app G)) := by
    rw [h]
    exact IsIso.id _
  have : IsIso (R.map (adj.counit.app G)) :=
    IsIso.of_isIso_comp_left (adj.unit.app (R.obj G)) _
  have : IsIso ((adj.counit.app G).hom.app (Opposite.op (⊤_ S.Etale))) := this
  exact spec_algClosed_etale_iso_of_terminal Ω (adj.counit.app G)

end AlgebraicGeometry.Scheme
