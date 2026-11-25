/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SimplicialHomObject
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.HypercoverOneMoreSimplex
import WeilConjectures.AlgebraicGeometry.SemiRepresentableCoveringPermanence
import WeilConjectures.AlgebraicTopology.SimplicialSetAddSimplices

/-!
# Local lifting along finite simplicial inclusions in a hypercover

Source: Stacks Project, Tag 01GN (Lemma 25.8.2), using Tag 01GM and unpacking Tag 01G3
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

private def pullFamily {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S T : SSet.{t}}
    {H : FormalCoproduct.{w} X.Etale} (v : SimplicialHomFamily K T H) (i : S ⟶ T) :
    SimplicialHomFamily K S H :=
  ⟨fun n s ↦ v.val n (i.app _ s), by
    intro m n φ s
    rw [v.property]
    exact congrArg (v.val m) (ConcreteCategory.congr_hom (i.naturality φ.op) s).symm⟩

private noncomputable def homFamilyMap {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S T : SSet.{t}}
    {H H' : FormalCoproduct.{w} X.Etale} (i : S ⟶ T)
    (v : SimplicialHomFamily K T H) {v' : SimplicialHomFamily K S H'}
    (hv' : (simplicialHomFamilyFunctor K S).IsRepresentedBy v') : H ⟶ H' :=
  (Equiv.ofBijective _ hv'.map_bijective).symm (pullFamily v i)

private theorem homFamilyMap_spec {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S T : SSet.{t}}
    {H H' : FormalCoproduct.{w} X.Etale} (i : S ⟶ T)
    (v : SimplicialHomFamily K T H) {v' : SimplicialHomFamily K S H'}
    (hv' : (simplicialHomFamilyFunctor K S).IsRepresentedBy v')
    (n : ℕ) (s : S.obj (op ⦋n⦌)) :
    homFamilyMap i v hv' ≫ v'.val n s = v.val n (i.app _ s) := by
  have h := (Equiv.ofBijective _ hv'.map_bijective).apply_symm_apply (pullFamily v i)
  exact congrArg (fun f : SimplicialHomFamily K S H ↦ f.val n s) h

private theorem homFamilyMap_comp {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {R S T : SSet.{t}}
    {HR HS HT : FormalCoproduct.{w} X.Etale} (i : R ⟶ S) (j : S ⟶ T)
    {u : SimplicialHomFamily K R HR} {v : SimplicialHomFamily K S HS}
    (z : SimplicialHomFamily K T HT)
    (hu : (simplicialHomFamilyFunctor K R).IsRepresentedBy u)
    (hv : (simplicialHomFamilyFunctor K S).IsRepresentedBy v) :
    homFamilyMap j z hv ≫ homFamilyMap i v hu = homFamilyMap (i ≫ j) z hu := by
  apply hu.map_bijective.injective
  apply Subtype.ext
  funext n s
  change (homFamilyMap j z hv ≫ homFamilyMap i v hu) ≫ u.val n s =
    homFamilyMap (i ≫ j) z hu ≫ u.val n s
  rw [Category.assoc, homFamilyMap_spec, homFamilyMap_spec, homFamilyMap_spec]
  rfl

private theorem represented_pullFamily_iso {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S T : SSet.{t}}
    {H : FormalCoproduct.{w} X.Etale} {v : SimplicialHomFamily K T H}
    (hv : (simplicialHomFamilyFunctor K T).IsRepresentedBy v) (i : S ≅ T) :
    (simplicialHomFamilyFunctor K S).IsRepresentedBy (pullFamily v i.hom) := by
  constructor
  intro W
  constructor
  · intro f g h
    apply hv.map_bijective.injective
    apply Subtype.ext
    funext n s
    have e := congrArg (fun a : SimplicialHomFamily K S W ↦
      a.val n (i.inv.app _ s)) h
    simpa [simplicialHomFamilyFunctor, SimplicialHomFamily.precomp, pullFamily,
      ← NatTrans.comp_app_apply] using e
  · intro a
    obtain ⟨f, hf⟩ := hv.map_bijective.surjective (pullFamily a i.inv)
    refine ⟨f, ?_⟩
    apply Subtype.ext
    funext n s
    have e := congrArg (fun b : SimplicialHomFamily K T W ↦
      b.val n (i.hom.app _ s)) hf
    simpa [simplicialHomFamilyFunctor, SimplicialHomFamily.precomp, pullFamily,
      ← NatTrans.comp_app_apply] using e

private theorem exists_representing_family {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t}) [S.Finite]
    (hne : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))) :
    ∃ (H : FormalCoproduct.{w} X.Etale) (v : SimplicialHomFamily K S H),
      (simplicialHomFamilyFunctor K S).IsRepresentedBy v := by
  obtain ⟨H, v, hv, huniv⟩ := exists_simplicial_hom_object X K S
    (fun n ↦ inferInstance) hne
  refine ⟨H, ⟨v, hv⟩, ⟨?_⟩⟩
  intro W
  constructor
  · intro f g h
    obtain ⟨l, hl, huniq⟩ := huniv W (fun n s ↦ f ≫ v n s) (by
      intro m n φ s
      rw [Category.assoc, hv])
    have hfg : ∀ n s, g ≫ v n s = f ≫ v n s := by
      intro n s
      exact (congrArg (fun a : SimplicialHomFamily K S W ↦ a.val n s) h).symm
    exact (huniq f (by intro n s; rfl)).trans (huniq g hfg).symm
  · intro a
    obtain ⟨f, hf, _⟩ := huniv W a.val a.property
    exact ⟨f, Subtype.ext (by funext n s; exact hf n s)⟩

private theorem covering_local_lifts {X : Scheme.{u}}
    {U V : FormalCoproduct.{w} X.Etale} (f : U ⟶ V)
    (hf : IsSemiRepresentableCovering f) (T : X.Etale) (a : semiRepresentablePoints T V) :
    ∃ (ι : Type w) (Tc : ι → X.Etale) (p : ∀ c : ι, Tc c ⟶ T),
      Sieve.ofArrows Tc p ∈ X.smallEtaleTopology T ∧
        ∃ b : ∀ c : ι, semiRepresentablePoints (Tc c) U,
          ∀ c : ι, b c ≫ f = (FormalCoproduct.incl X.Etale).map (p c) ≫ a := by
  obtain ⟨⟨j, a⟩, rfl⟩ := (FormalCoproduct.inclHomEquiv T V).symm.surjective a
  let I := {i : U.I // f.f i = j}
  let g : ∀ i : I, U.obj i.val ⟶ V.obj j := fun i ↦
    f.φ i.val ≫ eqToHom (congrArg V.obj i.property)
  refine ⟨I, (fun i ↦ pullback (g i) a), (fun i ↦ pullback.snd (g i) a), ?_,
    (fun i ↦ FormalCoproduct.Hom.fromIncl i.val (pullback.fst (g i) a)), ?_⟩
  · rw [Sieve.ofArrows_eq_pullback_of_isPullback g
      (fun i ↦ (IsPullback.of_hasPullback (g i) a).flip)]
    exact X.smallEtaleTopology.pullback_stable a (hf j)
  · intro i
    apply FormalCoproduct.hom_ext (by funext z; exact i.property)
    intro z
    change (pullback.fst (g i) a ≫ f.φ i.val) ≫
      eqToHom (congrArg V.obj i.property) = pullback.snd (g i) a ≫ a
    simpa only [Category.assoc] using (pullback.condition (f := g i) (g := a))

private theorem covering_of_section {X : Scheme.{u}}
    {U V : FormalCoproduct.{w} X.Etale} (f : U ⟶ V) (s : V ⟶ U)
    (h : s ≫ f = 𝟙 V) : IsSemiRepresentableCovering f := by
  intro j
  obtain ⟨e, he⟩ := (FormalCoproduct.hom_ext_iff' _ _).mp h j
  let i : {i : U.I // f.f i = j} := ⟨s.f j, e⟩
  have hm := Sieve.ofArrows_mk
    (fun i : {i : U.I // f.f i = j} ↦ U.obj i.val)
    (fun i ↦ f.φ i.val ≫ eqToHom (congrArg V.obj i.property)) i
  have hm' := (Sieve.ofArrows _ _).downward_closed hm (s.φ j)
  have he' : s.φ j ≫ (f.φ (s.f j) ≫ eqToHom (congrArg V.obj e)) = 𝟙 (V.obj j) := by
    change (s.φ j ≫ f.φ (s.f j)) ≫ eqToHom (congrArg V.obj e) = 𝟙 _ at he
    simpa only [Category.assoc] using he
  rw [he'] at hm'
  rw [Sieve.id_mem_iff_eq_top.mp hm']
  exact X.smallEtaleTopology.top_mem _

private theorem covering_homFamilyMap_iso {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S T : SSet.{t}}
    {H H' : FormalCoproduct.{w} X.Etale} (i : S ≅ T)
    (v : SimplicialHomFamily K T H) {v' : SimplicialHomFamily K S H'}
    (hv : (simplicialHomFamilyFunctor K T).IsRepresentedBy v)
    (hv' : (simplicialHomFamilyFunctor K S).IsRepresentedBy v') :
    IsSemiRepresentableCovering (homFamilyMap i.hom v hv') := by
  apply covering_of_section _ (homFamilyMap i.inv v' hv)
  apply hv'.map_bijective.injective
  apply Subtype.ext
  funext n s
  change (homFamilyMap i.inv v' hv ≫ homFamilyMap i.hom v hv') ≫ v'.val n s =
    (𝟙 H') ≫ v'.val n s
  rw [Category.assoc, homFamilyMap_spec, homFamilyMap_spec, Category.id_comp]
  exact congrArg (v'.val n) (ConcreteCategory.congr_hom (congr_app i.hom_inv_id _) s)

private def nestedIso {B : SSet.{t}} {U V : B.Subcomplex} (h : U ≤ V) :
    (U.preimage V.ι).toSSet ≅ U.toSSet where
  hom :=
    { app := fun n ↦ ↾fun s ↦ ⟨s.val.val, s.property⟩
      naturality := by intros; rfl }
  inv :=
    { app := fun n ↦ ↾fun s ↦ ⟨⟨s.val, h _ s.property⟩, s.property⟩
      naturality := by intros; rfl }
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

private theorem covering_one_step {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) {B : SSet.{t}} [B.Finite]
    {U V : B.Subcomplex} (hUV : U ≤ V)
    (hneU : ∀ n : ℕ, Nonempty (U.toSSet.obj (op ⦋n⦌)))
    (hneV : ∀ n : ℕ, Nonempty (V.toSSet.obj (op ⦋n⦌)))
    (n : ℕ) (x : V.toSSet.obj (op ⦋n⦌))
    (hx : x.val ∉ Set.range (U.ι.app (op ⦋n⦌)))
    (hlower : ∀ i : ℕ, i < n → Set.range (V.ι.app (op ⦋i⦌)) =
      Set.range (U.ι.app (op ⦋i⦌)))
    (hdegree : Set.range (V.ι.app (op ⦋n⦌)) =
      Set.range (U.ι.app (op ⦋n⦌)) ∪ {x.val})
    (hhigher : ∀ (j : ℕ) (z : V.toSSet.obj (op ⦋j⦌)), n < j →
      z.val ∉ Set.range (U.ι.app (op ⦋j⦌)) → z ∈ V.toSSet.degenerate j)
    {HV HU : FormalCoproduct.{w} X.Etale}
    (v : SimplicialHomFamily K V.toSSet HV) (u : SimplicialHomFamily K U.toSSet HU)
    (hv : (simplicialHomFamilyFunctor K V.toSSet).IsRepresentedBy v)
    (hu : (simplicialHomFamilyFunctor K U.toSSet).IsRepresentedBy u) :
    IsSemiRepresentableCovering (homFamilyMap (SSet.Subcomplex.homOfLE hUV) v hu) := by
  let C := U.preimage V.ι
  let u' := pullFamily u (nestedIso hUV).hom
  have hu' := represented_pullFamily_iso hu (nestedIso hUV)
  have hneC : ∀ i : ℕ, Nonempty (C.toSSet.obj (op ⦋i⦌)) := by
    intro i
    obtain ⟨s⟩ := hneU i
    exact ⟨(nestedIso hUV).inv.app _ s⟩
  have hx' : x ∉ C.obj (op ⦋n⦌) := by
    intro h
    exact hx ⟨⟨x.val, h⟩, rfl⟩
  have hlower' : ∀ i : ℕ, i < n → C.obj (op ⦋i⦌) = Set.univ := by
    intro i hi
    ext s
    simp only [Set.mem_univ, iff_true]
    have hs : s.val ∈ Set.range (U.ι.app (op ⦋i⦌)) := by
      rw [← hlower i hi]
      exact ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := hs
    change s.val ∈ U.obj _
    rw [← hs']
    exact s'.property
  have hdegree' : (Set.univ : Set (V.toSSet.obj (op ⦋n⦌))) = C.obj (op ⦋n⦌) ∪ {x} := by
    ext s
    simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, true_iff]
    have hs : s.val ∈ Set.range (U.ι.app (op ⦋n⦌)) ∪ {x.val} := by
      rw [← hdegree]
      exact ⟨s, rfl⟩
    rcases hs with ⟨s', hs'⟩ | hs
    · apply Or.inl
      change s.val ∈ U.obj _
      rw [← hs']
      exact s'.property
    · exact Or.inr (Subtype.ext hs)
  have hhigher' : ∀ (j : ℕ) (z : V.toSSet.obj (op ⦋j⦌)), n < j →
      z ∉ C.obj (op ⦋j⦌) → z ∈ V.toSSet.degenerate j := by
    intro j z hj hz
    apply hhigher j z hj
    rintro ⟨z', hz'⟩
    apply hz
    change z.val ∈ U.obj _
    rw [← hz']
    exact z'.property
  have hc := isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex
    K hK V.toSSet C (fun i ↦ ⟨inferInstance, hneV i⟩)
    (fun i ↦ ⟨inferInstance, hneC i⟩) n x hx' hlower' hdegree' hhigher' v u' hv hu'
  have heq : simplicialHomRestriction C v hu' =
      homFamilyMap (SSet.Subcomplex.homOfLE hUV) v hu := by
    apply hu.map_bijective.injective
    apply Subtype.ext
    funext i s
    have hspec := homFamilyMap_spec C.ι v hu' i ((nestedIso hUV).inv.app _ s)
    change simplicialHomRestriction C v hu' ≫ u.val i s =
      homFamilyMap (SSet.Subcomplex.homOfLE hUV) v hu ≫ u.val i s
    rw [homFamilyMap_spec]
    exact hspec
  rwa [heq] at hc

/-- Restriction along a finite simplicial inclusion is a covering and admits local lifts
of every étale test object's point. The Hom objects are arbitrary representing pairs for
`simplicialHomFamilyFunctor`, so the assertion applies to the fixed choices of those pairs.
Source: Stacks Project, Tag 01GN, with the local-lifting clause unpacked from Tag 01G3
(auxiliary; not a blueprint node).

Proof:
1. By lem-weil-pbc-simplicial-set-add-simplices (Stacks 018S), insert finitely many
   nondegenerate simplices one at a time between `A` and `B`. Every intermediate subset
   has finite nonempty degrees, since it lies between `A` and `B`. Its nondegenerate
   simplices remain nondegenerate in `B`: a degeneracy of a simplex in the subset has
   its ancestor in that subset by applying an order-preserving section of the surjection
   in the epi-mono factorization. Thus each intermediate subset is finite.
2. Apply lem-weil-pbc-hypercover-one-more-simplex (01GM) to each extension. Its
   restriction map is a covering by the matching-cover condition on `K`.
3. The universal property in def-weil-pbc-simplicial-hom-object identifies the full
   restriction with the composite of those maps. Coverings are closed under composition
   by lem-weil-pbc-semi-representable-covering-permanence (01G4). For a chain of length
   zero it is the identity, which is a covering in def-weil-pbc-etale-site.
4. Write a test point as `(j, a : T → H_A.obj j)` using
   def-weil-pbc-semi-representable-object. Pull back the covering components over `j`
   along `a`. By lem-weil-pbc-etale-covering-base-change the projections form an étale
   covering of `T`; the other projections are points of `H_B`, and the pullback equation
   says their restrictions are the pullbacks of `a`. -/
theorem hypercover_finite_simplex_lifting (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) (B : SSet.{t}) (A : B.Subcomplex)
    [B.Finite] [A.toSSet.Finite]
    (hBfinite : ∀ n : ℕ, Finite (B.obj (op ⦋n⦌)))
    (hBnonempty : ∀ n : ℕ, Nonempty (B.obj (op ⦋n⦌)))
    (hAfinite : ∀ n : ℕ, Finite (A.toSSet.obj (op ⦋n⦌)))
    (hAnonempty : ∀ n : ℕ, Nonempty (A.toSSet.obj (op ⦋n⦌)))
    (H_B H_A : FormalCoproduct.{w} X.Etale)
    (uB : SimplicialHomFamily K B H_B)
    (uA : SimplicialHomFamily K A.toSSet H_A)
    (huB : (simplicialHomFamilyFunctor K B).IsRepresentedBy uB)
    (huA : (simplicialHomFamilyFunctor K A.toSSet).IsRepresentedBy uA) :
    IsSemiRepresentableCovering (simplicialHomRestriction A uB huA) ∧
      ∀ (T : X.Etale) (a : semiRepresentablePoints T H_A),
        ∃ (ι : Type w) (Tc : ι → X.Etale) (p : ∀ c : ι, Tc c ⟶ T),
          Sieve.ofArrows Tc p ∈ X.smallEtaleTopology T ∧
            ∃ b : ∀ c : ι, semiRepresentablePoints (Tc c) H_B,
              ∀ c : ι, b c ≫ simplicialHomRestriction A uB huA =
                (FormalCoproduct.incl X.Etale).map (p c) ≫ a := by
  classical
  have hnetop : ∀ n : ℕ, Nonempty ((⊤ : B.Subcomplex).toSSet.obj (op ⦋n⦌)) := by
    intro n
    obtain ⟨s⟩ := hBnonempty n
    exact ⟨⟨s, Set.mem_univ _⟩⟩
  obtain ⟨r, W, h0, hr, hW, hsteps⟩ := SSet.add_simplices B A ⊤ le_top
    hAfinite (fun n ↦ @Finite.of_injective _ _ (hBfinite n) Subtype.val
      Subtype.val_injective) hAnonempty hnetop
  have hmono : Monotone W := Fin.monotone_iff_le_succ.mpr hW
  have hAW (k : Fin (r + 1)) : A ≤ W k := by
    rw [← h0]
    exact hmono (Fin.zero_le k)
  have hneW (k : Fin (r + 1)) (n : ℕ) : Nonempty ((W k).toSSet.obj (op ⦋n⦌)) := by
    obtain ⟨s⟩ := hAnonempty n
    exact ⟨⟨s.val, hAW k _ s.property⟩⟩
  have hex (k : Fin (r + 1)) := exists_representing_family K (W k).toSSet (hneW k)
  choose H v hv using hex
  have hc (k : Fin (r + 1)) : IsSemiRepresentableCovering
      (homFamilyMap (SSet.Subcomplex.homOfLE (hAW k)) (v k) huA) := by
    induction k using Fin.induction with
    | zero =>
      exact covering_homFamilyMap_iso (SSet.Subcomplex.eqToIso h0.symm) (v 0) (hv 0) huA
    | succ k ih =>
      obtain ⟨n, x, hx, hl, hd, hh⟩ := hsteps k
      have hstep := covering_one_step K hK (hW k) (hneW k.castSucc) (hneW k.succ)
        n x hx hl hd hh (v k.succ) (v k.castSucc) (hv k.succ) (hv k.castSucc)
      have hcomp := (semiRepresentableCovering_comp_baseChange _ hstep).1 _ ih
      rw [homFamilyMap_comp] at hcomp
      exact hcomp
  let last : Fin (r + 1) := ⟨r, Nat.lt_succ_self r⟩
  let e : (W last).toSSet ≅ B := SSet.Subcomplex.eqToIso hr ≪≫ SSet.Subcomplex.topIso B
  have he : SSet.Subcomplex.homOfLE (hAW last) ≫ e.hom = A.ι := by
    ext n s
    rfl
  have hecov := covering_homFamilyMap_iso e uB huB (hv last)
  have hcov := (semiRepresentableCovering_comp_baseChange _ hecov).1 _ (hc last)
  rw [homFamilyMap_comp, he] at hcov
  change IsSemiRepresentableCovering (simplicialHomRestriction A uB huA) at hcov
  exact ⟨hcov, covering_local_lifts _ hcov⟩

end AlgebraicGeometry.Scheme
