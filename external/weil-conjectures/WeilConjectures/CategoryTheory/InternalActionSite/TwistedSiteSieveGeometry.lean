/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic

/-!
# Labeled pullbacks and sieves of the internal action category

Source: the agent-formulated categorical foundation motivated by main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3); Stacks Sites, Tags 00VH, 00Z4,
00ZD for the site and topology axioms (blueprint: lem-sfb-twisted-site-sieve-geometry).

The existing `InternalActionSite.Object`, `Arrow`, `categoryStruct`, `category`,
`projection`, `precoverage`, and `topology` give the actual construction. In particular,
composition of `(g,b)` followed by `(f,a)` has label `b * K.map g.op a`.
The theorem supplies the explicit pullbacks, source normalization, and sieve geometry
for that same category, without introducing a second category or a second precoverage.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

private theorem comp_label {X Y Z : Object K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).label = f.label * K.map f.base.op g.label := rfl

private theorem vertical_inverse (X : Object K) (a : K.obj (op X.base)) :
    (Arrow.mk (𝟙 X.base) a : X ⟶ X) ≫ Arrow.mk (𝟙 X.base) a⁻¹ = 𝟙 X := by
  apply arrow_ext K
  · exact Category.id_comp _
  · change a * K.map (𝟙 X.base).op a⁻¹ = 1
    simp

private theorem normalize {X Y : Object K} (f : X ⟶ Y) :
    (Arrow.mk (𝟙 X.base) f.label : X ⟶ X) ≫ Arrow.mk f.base 1 = f := by
  apply arrow_ext K
  · exact Category.id_comp _
  · change f.label * K.map (𝟙 X.base).op 1 = f.label
    simp

private theorem label_iff {X Y : Object K} (S : Sieve X) (f : Y ⟶ X) :
    S f ↔ S (Arrow.mk f.base 1 : Y ⟶ X) := by
  constructor
  · intro hf
    have h := S.downward_closed hf (Arrow.mk (𝟙 Y.base) f.label⁻¹ : Y ⟶ Y)
    have he : (Arrow.mk (𝟙 Y.base) f.label⁻¹ : Y ⟶ Y) ≫ f =
        Arrow.mk f.base 1 := by
      apply arrow_ext K
      · exact Category.id_comp _
      · change f.label⁻¹ * K.map (𝟙 Y.base).op f.label = 1
        simp
    rwa [he] at h
  · intro hf
    simpa only [normalize K f] using
      S.downward_closed hf (Arrow.mk (𝟙 Y.base) f.label : Y ⟶ Y)

private def baseSieve {X : Object K} (S : Sieve X) : Sieve X.base where
  arrows := fun _ f ↦ S (Arrow.mk f 1)
  downward_closed := by
    intro Y Z f hf g
    have h := S.downward_closed hf
      (Arrow.mk g 1 : Object.mk (K := K) Z ⟶ Object.mk (K := K) Y)
    change S (Arrow.mk (g ≫ f) (1 * K.map g.op 1)) at h
    simpa only [map_one, mul_one] using h

private def liftSieve {X : Object K} (T : Sieve X.base) : Sieve X where
  arrows := fun _ f ↦ T f.base
  downward_closed := fun hf g ↦ T.downward_closed hf g.base

private def sieveEquiv (X : Object K) : Sieve X ≃o Sieve X.base where
  toFun := baseSieve K
  invFun := liftSieve K
  left_inv S := Sieve.ext fun _ f ↦ (label_iff K S f).symm
  right_inv T := rfl
  map_rel_iff' := by
    intro S T
    constructor
    · intro h Y f hf
      exact (label_iff K T f).mpr (h _ ((label_iff K S f).mp hf))
    · intro h Y f hf
      exact h _ hf

private theorem base_pullback {X Y : Object K} (f : Y ⟶ X) (S : Sieve X) :
    baseSieve K (S.pullback f) = (baseSieve K S).pullback f.base := by
  apply Sieve.ext
  intro Z g
  change S ((Arrow.mk g 1 : Object.mk (K := K) Z ⟶ Y) ≫ f) ↔ S (Arrow.mk (g ≫ f.base) 1)
  exact label_iff K S _

private theorem base_generate (X : Object K) (I : Type u)
    (U : I → Object K) (a : ∀ i, U i ⟶ X) :
    baseSieve K (Sieve.generate (Presieve.ofArrows U a)) =
      Sieve.generate (Presieve.ofArrows (fun i ↦ (U i).base) (fun i ↦ (a i).base)) := by
  apply Sieve.ext
  intro Y f
  constructor
  · rintro ⟨Z, h, g, hg, he⟩
    obtain ⟨i⟩ := hg
    exact ⟨(U i).base, h.base, (a i).base, Presieve.ofArrows.mk i,
      congrArg Arrow.base he⟩
  · rintro ⟨Z, h, g, hg, he⟩
    obtain ⟨i⟩ := hg
    refine ⟨U i, Arrow.mk h (K.map h.op (a i).label)⁻¹, a i,
      Presieve.ofArrows.mk i, ?_⟩
    apply arrow_ext K he
    simp [comp_label]

private def topologyUp (H : GrothendieckTopology C) : GrothendieckTopology (Object K) where
  sieves X := {S | baseSieve K S ∈ H X.base}
  top_mem' X := H.top_mem X.base
  pullback_stable' := by
    intro X Y S f hS
    change baseSieve K (S.pullback f) ∈ H Y.base
    rw [base_pullback]
    exact H.pullback_stable f.base hS
  transitive' := by
    intro X S hS R hR
    apply H.transitive hS (baseSieve K R)
    intro Y f hf
    have hh := hR (f := (Arrow.mk f 1 : Object.mk (K := K) Y ⟶ X)) hf
    change baseSieve K (R.pullback (Arrow.mk f 1)) ∈ H Y at hh
    rwa [base_pullback] at hh

private def topologyDown (L : GrothendieckTopology (Object K)) : GrothendieckTopology C where
  sieves X := {T | liftSieve K (X := Object.mk (K := K) X) T ∈ L (Object.mk (K := K) X)}
  top_mem' X := L.top_mem (Object.mk (K := K) X)
  pullback_stable' := by
    intro X Y S f hS
    exact L.pullback_stable (Arrow.mk f 1 : Object.mk (K := K) Y ⟶ Object.mk (K := K) X) hS
  transitive' := by
    intro X S hS R hR
    apply L.transitive hS (liftSieve K R)
    intro Y f hf
    cases Y with
    | mk Y => exact hR hf

private theorem image_presieve {X : Object K} (R : Presieve X) :
    (fun Y (f : Y ⟶ X.base) ↦ ∃ a, R (Arrow.mk f a)) = R.map (projection K) := by
  funext Y f
  apply propext
  constructor
  · rintro ⟨a, ha⟩
    exact Presieve.map_map (F := projection K) (f := (Arrow.mk f a : Object.mk (K := K) Y ⟶ X)) ha
  · intro hh
    obtain ⟨Z, hZ, g, hg, he⟩ := Presieve.map_iff.mp hh
    cases Z with
    | mk Z =>
      change Z = Y at hZ
      subst Y
      simp only [eqToHom_refl, Category.id_comp] at he
      change g.base = f at he
      cases g with
      | mk gb ga =>
        dsimp at he
        subst f
        exact ⟨ga, hg⟩

private theorem precoverage_eq (J : Precoverage C) :
    precoverage K J = J.comap (projection K) := by
  apply Precoverage.ext
  funext X
  ext R
  change ((fun Y (f : Y ⟶ X.base) ↦ ∃ a, R (Arrow.mk f a)) ∈ J X.base) ↔ _
  rw [image_presieve]
  rfl

private theorem covering_family_iff (J : Precoverage C) (I : Type u) (X : Object K)
    (U : I → Object K) (a : ∀ i, U i ⟶ X) :
    Presieve.ofArrows U a ∈ precoverage K J X ↔
      Presieve.ofArrows (fun i ↦ (U i).base) (fun i ↦ (a i).base) ∈ J X.base := by
  rw [precoverage_eq, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  rfl

private theorem lifted_covers (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (I : Type u) (X : Object K) (U : I → Object K) (a : ∀ i, U i ⟶ X)
    (ha : Presieve.ofArrows U a ∈ precoverage K J X) (Y : Object K) (b : Y ⟶ X) :
    ∃ (P : I → Object K) (p : ∀ i, P i ⟶ Y) (q : ∀ i, P i ⟶ U i),
      (∀ i, IsPullback (p i) (q i) b (a i)) ∧
        Presieve.ofArrows P p ∈ precoverage K J Y := by
  obtain ⟨P, p, q, hp, hc⟩ := hJ.2.2 I X.base (fun i ↦ (U i).base)
    (fun i ↦ (a i).base) ((covering_family_iff K J I X U a).mp ha) Y.base b.base
  refine ⟨(fun i ↦ Object.mk (P i)), (fun i ↦ Arrow.mk (p i) 1),
    (fun i ↦ Arrow.mk (q i) (K.map (p i).op b.label *
      (K.map (q i).op (a i).label)⁻¹)), ?_, ?_⟩
  · intro i
    exact labeled_pullback K b (a i) (p i) (q i) (hp i)
  · exact (covering_family_iff K J I Y _ _).mpr hc

private theorem base_generate_presieve (X : Object K) (R : Presieve X) :
    baseSieve K (Sieve.generate R) = Sieve.generate (R.map (projection K)) := by
  obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows]
  exact base_generate K X I U a

private theorem generated_topology (J : Precoverage C) (X : Object K) (S : Sieve X) :
    S ∈ topology K J X ↔ baseSieve K S ∈ J.toGrothendieck X.base := by
  have hup : (precoverage K J).toGrothendieck ≤ topologyUp K J.toGrothendieck := by
    rw [Precoverage.toGrothendieck_eq_sInf]
    apply sInf_le
    intro Y R hR
    change baseSieve K (Sieve.generate R) ∈ J.toGrothendieck Y.base
    rw [base_generate_presieve]
    apply Precoverage.generate_mem_toGrothendieck
    rw [precoverage_eq, Precoverage.mem_comap_iff] at hR
    exact hR
  have hdown : J.toGrothendieck ≤ topologyDown K (topology K J) := by
    rw [Precoverage.toGrothendieck_eq_sInf]
    apply sInf_le
    intro Y R hR
    obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
    let V : I → Object K := fun i ↦ Object.mk (U i)
    let b : ∀ i, V i ⟶ Object.mk (K := K) Y := fun i ↦ Arrow.mk (a i) 1
    have hb : Presieve.ofArrows V b ∈ precoverage K J (Object.mk (K := K) Y) :=
      (covering_family_iff K J I (Object.mk (K := K) Y) V b).mpr hR
    change liftSieve K (Sieve.generate (Presieve.ofArrows U a)) ∈
      topology K J (Object.mk (K := K) Y)
    rw [← base_generate K (Object.mk (K := K) Y) I V b]
    change (sieveEquiv K (Object.mk (K := K) Y)).symm
      (sieveEquiv K (Object.mk (K := K) Y) (Sieve.generate (Presieve.ofArrows V b))) ∈ _
    rw [(sieveEquiv K (Object.mk (K := K) Y)).symm_apply_apply]
    exact Precoverage.generate_mem_toGrothendieck hb
  constructor
  · exact fun h ↦ hup _ h
  · intro h
    have hh := hdown _ h
    cases X with
    | mk X =>
      change liftSieve K (baseSieve K S) ∈ topology K J (Object.mk (K := K) X) at hh
      change (sieveEquiv K (Object.mk (K := K) X)).symm
        (sieveEquiv K (Object.mk (K := K) X) S) ∈ _ at hh
      rwa [(sieveEquiv K (Object.mk (K := K) X)).symm_apply_apply] at hh

set_option linter.unusedVariables false in
/-- Labeled pullbacks, normalization, sieve correspondence and generated covering topology.

Source: agent-formulated categorical foundation for main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3); Stacks Sites 00VH, 00Z4, 00ZD
for the background axioms (blueprint: lem-sfb-twisted-site-sieve-geometry).
The twisted construction itself is an agent lemma; no external theorem asserting this
whole construction is claimed.

Proof: (1) The existing object and arrow types are small dependent products/sums in `u`.
(2) For three arrows both compositions have label `c * h^*(b * g^*a)`, equal to
`(c * h^*b) * (gh)^*a` by the homomorphism and functor laws. Identity restrictions and
the group unit laws give the category identities. The projection forgets the label.
(3) The vertical arrows with labels `a` and `a⁻¹` are inverse, and `(f,a)` is the
composite of the vertical arrow `(1,a)` with `(f,1)`, giving source normalization.
(4) Given a base pullback with legs `p,q`, put `k = p^*a * (q^*b)⁻¹`. The lifted legs
`(p,1),(q,k)` have equal composites because `k * q^*b = p^*a`.
(5) A cone `(r,c),(s,d)` satisfies `c * r^*a = d * s^*b`. Its unique base lift `t`
with label `c` has second composite label `c * t^*k = d`. The first leg forces the
label, and base universality forces `t`, proving the full pullback property.
(6) Apply the existing `hasIsos K J hJ` theorem for singleton isomorphism covers.
Apply `hJ.2.2` to an underlying covering family, and lift its chosen pullbacks as
in (4)-(5). Their underlying arrows form that chosen base cover. No bind-composition
closure of the lifted precoverage is used or asserted.
(7) Precomposition by `(1,a)` and its inverse shows that sieve membership is independent
of the label. Thus taking label-one arrows and taking all labels over a base sieve
are mutually inverse, inclusion-preserving operations. They preserve the maximal sieve.
(8) The composite of `(h,1)` with `(g,b)` has base `h ≫ g`; label independence shows
that the sieve correspondence commutes with pullback along `(g,b)` and `g`.
(9) A factorization of a base arrow through `f_i` lifts with prescribed final label `a`
by giving the preceding arrow the label `a * (h^*a_i)⁻¹`. Hence generated sieves
correspond, including for an empty family.
(10) Transport any base topology by this sieve correspondence. Maximality and pullback
stability follow from (7)-(8). For local character, test the twisted hypothesis on
label-one lifts and apply base local character. (11) Conversely transport a twisted
topology to the base; all labels have the same pullback sieve under the correspondence,
so its local character gives the base local-character axiom. These transports are inverse.
(12) The least topology containing prescribed generating sieves is their intersection
over all containing topologies, as expressed by `Precoverage.toGrothendieck`.
(13) By (9) the transported base generated topology contains all twisted generators;
conversely every base generator has a label-one lift among the twisted generators.
The least properties give both inclusions and the final covering-sieve criterion. -/
theorem sieve_geometry [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    (∀ (X : Object K) (a : K.obj (op X.base)),
      (Arrow.mk (𝟙 X.base) a : X ⟶ X) ≫ Arrow.mk (𝟙 X.base) a⁻¹ = 𝟙 X ∧
      (Arrow.mk (𝟙 X.base) a⁻¹ : X ⟶ X) ≫ Arrow.mk (𝟙 X.base) a = 𝟙 X) ∧
    (∀ (X Y : Object K) (f : X ⟶ Y),
      ∃ e : X ≅ X, e.hom = Arrow.mk (𝟙 X.base) f.label ∧
        e.inv = Arrow.mk (𝟙 X.base) f.label⁻¹ ∧
        f = e.hom ≫ Arrow.mk f.base 1) ∧
    (∀ (U V W P : Object K) (f : V ⟶ U) (g : W ⟶ U)
      (p : P.base ⟶ V.base) (q : P.base ⟶ W.base),
      IsPullback p q f.base g.base →
        IsPullback (Arrow.mk p 1 : P ⟶ V)
          (Arrow.mk q (K.map p.op f.label * (K.map q.op g.label)⁻¹) : P ⟶ W) f g) ∧
    (precoverage K J).HasIsos ∧
    (∀ (I : Type u) (X : Object K) (U : I → Object K) (a : ∀ i, U i ⟶ X),
      Presieve.ofArrows U a ∈ precoverage K J X →
      ∀ (Y : Object K) (b : Y ⟶ X),
        ∃ (P : I → Object K) (p : ∀ i, P i ⟶ Y) (q : ∀ i, P i ⟶ U i),
          (∀ i, IsPullback (p i) (q i) b (a i)) ∧
            Presieve.ofArrows P p ∈ precoverage K J Y) ∧
    ∃ e : ∀ X : Object K, Sieve X ≃o Sieve X.base,
      (∀ (X : Object K) (S : Sieve X) (Y : C) (f : Y ⟶ X.base),
        e X S f ↔ S (Arrow.mk f 1)) ∧
      (∀ (X : Object K) (T : Sieve X.base) (Y : Object K) (f : Y ⟶ X),
        (e X).symm T f ↔ T f.base) ∧
      (∀ X : Object K, e X ⊤ = ⊤) ∧
      (∀ (X Y : Object K) (f : Y ⟶ X) (S : Sieve X),
        e Y (S.pullback f) = (e X S).pullback f.base) ∧
      (∀ (X : Object K) (I : Type u) (U : I → Object K) (a : ∀ i, U i ⟶ X),
        e X (Sieve.generate (Presieve.ofArrows U a)) =
          Sieve.generate (Presieve.ofArrows (fun i ↦ (U i).base) (fun i ↦ (a i).base))) ∧
      (∀ H : GrothendieckTopology C, ∃ L : GrothendieckTopology (Object K),
        ∀ (X : Object K) (S : Sieve X), S ∈ L X ↔ e X S ∈ H X.base) ∧
      (∀ L : GrothendieckTopology (Object K), ∃ H : GrothendieckTopology C,
        ∀ (X : Object K) (T : Sieve X.base), T ∈ H X.base ↔ (e X).symm T ∈ L X) ∧
      (∀ (X : Object K) (S : Sieve X),
        S ∈ topology K J X ↔ e X S ∈ J.toGrothendieck X.base) := by
  refine ⟨?_, ?_, ?_, hasIsos K J hJ, lifted_covers K J hJ, sieveEquiv K, ?_⟩
  · intro X a
    exact ⟨vertical_inverse K X a, by simpa using vertical_inverse K X a⁻¹⟩
  · intro X Y f
    refine ⟨⟨Arrow.mk (𝟙 X.base) f.label, Arrow.mk (𝟙 X.base) f.label⁻¹,
      vertical_inverse K X f.label, ?_⟩, rfl, rfl, (normalize K f).symm⟩
    simpa using vertical_inverse K X f.label⁻¹
  · exact fun U V W P f g p q hp ↦ labeled_pullback K f g p q hp
  · refine ⟨(fun _ _ _ _ ↦ Iff.rfl), (fun _ _ _ _ ↦ Iff.rfl),
      (fun _ ↦ rfl), (fun _ _ f S ↦ base_pullback K f S), base_generate K, ?_, ?_,
      generated_topology K J⟩
    · intro H
      exact ⟨topologyUp K H, fun _ _ ↦ Iff.rfl⟩
    · intro L
      refine ⟨topologyDown K L, ?_⟩
      intro X T
      cases X
      rfl

end CategoryTheory.InternalActionSite
