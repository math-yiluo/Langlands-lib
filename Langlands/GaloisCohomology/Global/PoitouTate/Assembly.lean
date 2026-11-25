import Langlands.GaloisCohomology.Global.PoitouTate.Hypotheses
import Langlands.GaloisCohomology.Global.PoitouTate.DualityStatement
import Langlands.GaloisCohomology.Global.PoitouTate.NineTermStatement
import Langlands.GaloisCohomology.Global.PoitouTate.ShaStatement

/-!
# Poitou–Tate for `G_S` from the abstract hypotheses

Given the hypotheses `TatePoitouTateHypotheses` of the abstract nine-term sequence for `G_S`
(`tatePoitouTateHypotheses_of`), the three conclusions of Poitou–Tate duality for a finite module `M`
killed by `N` follow from the abstract theorems: `isDuality_of_hypotheses`,
`isNineTermExact_of_hypotheses`, `isShaDuality_of_hypotheses`. For `N = 1` the module is zero and
everything holds for trivial reasons (`isDuality_of_subsingleton`, `isNineTermExact_of_subsingleton`,
`isShaDuality_of_subsingleton`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Subsingleton

/-- An additive map between subsingletons is bijective. -/
theorem bijective_of_subsingleton {A B : Type*} [AddZeroClass A] [AddZeroClass B] [Subsingleton A]
    [Subsingleton B] (f : A →+ B) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- Additive maps are exact at a subsingleton. -/
theorem exact_of_subsingleton {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [Subsingleton B] (f : A →+ B) (g : B →+ C) : Function.Exact f g := fun y => by
  rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun _ => ⟨0, map_zero f⟩, fun _ => rfl⟩

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction of a subsingleton module is a subsingleton. -/
theorem subsingleton_res {H : Type u} [Group H] (φ : H →* G) (A : Rep.{u} k G) [Subsingleton A] :
    Subsingleton (Rep.res φ A) :=
  inferInstanceAs (Subsingleton A)

/-- The modified cohomology with compact support of a subsingleton module is a subsingleton. -/
theorem subsingleton_tateCompactCohomologyRes {ι : Type u} {Hv : ι → Type u}
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (φ : ∀ v, Hv v →ₜ* G) {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)]
    [∀ w, TopologicalSpace (F w)] [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)]
    (ψ : ∀ w, F w →ₜ* G) (A : Rep.{u} k G) [IsSmoothRep A] [Subsingleton A] (n : ℕ) :
    Subsingleton (tateCompactCohomologyRes φ ψ A n) := by
  have h1 : (𝟙 A : A ⟶ A) = 0 := Rep.hom_ext (Representation.IntertwiningMap.ext
    (LinearMap.ext fun _ => Subsingleton.elim _ _))
  refine ⟨fun x y => ?_⟩
  have hx : (tateCompactCohomologyResMap φ ψ (𝟙 A) n).hom x =
      (tateCompactCohomologyResMap φ ψ (0 : A ⟶ A) n).hom x := by rw [h1]
  have hy : (tateCompactCohomologyResMap φ ψ (𝟙 A) n).hom y =
      (tateCompactCohomologyResMap φ ψ (0 : A ⟶ A) n).hom y := by rw [h1]
  rw [tateCompactCohomologyResMap_id, tateCompactCohomologyResMap_zero] at hx hy
  exact hx.trans hy.symm

/-- Bijectivity of a pairing is preserved by composing both arguments with isomorphisms. -/
theorem bijective_comp_compl₂ {A A' B B' C : Type*} [AddCommGroup A] [AddCommGroup A']
    [AddCommGroup B] [AddCommGroup B'] [AddCommGroup C] (f : A →+ B →+ C) (e : A' ≃+ A)
    (e' : B' ≃+ B) (hf : Function.Bijective f) :
    Function.Bijective ((f.comp e.toAddMonoidHom).compl₂ e'.toAddMonoidHom) := by
  have hpre : Function.Bijective fun g : B →+ C => g.comp e'.toAddMonoidHom :=
    Function.bijective_iff_has_inverse.2 ⟨fun g => g.comp e'.symm.toAddMonoidHom,
      fun g => AddMonoidHom.ext fun b => by simp, fun g => AddMonoidHom.ext fun b => by simp⟩
  exact (hpre.comp hf).comp e.bijective

/-- Bijectivity of the flipped pairing is preserved by composing both arguments with
isomorphisms. -/
theorem bijective_comp_compl₂_flip {A A' B B' C : Type*} [AddCommGroup A] [AddCommGroup A']
    [AddCommGroup B] [AddCommGroup B'] [AddCommGroup C] (f : A →+ B →+ C) (e : A' ≃+ A)
    (e' : B' ≃+ B) (hf : Function.Bijective f.flip) :
    Function.Bijective ((f.comp e.toAddMonoidHom).compl₂ e'.toAddMonoidHom).flip := by
  have h := bijective_comp_compl₂ f.flip e' e hf
  convert h using 1
  funext y
  ext x
  rfl

/-- `AddSubgroup.inclusion` along an equality is `AddEquiv.addSubgroupCongr`. -/
theorem inclusion_eq_addSubgroupCongr {G : Type*} [AddGroup G] {H H' : AddSubgroup G}
    (h : H = H') : AddSubgroup.inclusion h.le = (AddEquiv.addSubgroupCongr h).toAddMonoidHom :=
  rfl

end Subsingleton

section Trivial

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- The dual of a module killed by `1` is a subsingleton. -/
instance subsingleton_dual_one [Subsingleton M] : Subsingleton (dual 1 M) := by
  refine ⟨fun f g => LinearMap.ext fun m => ?_⟩
  rw [Subsingleton.elim m 0, map_zero, map_zero]

variable [Subsingleton M]

/-- For `M = 0` duality holds trivially. -/
theorem isDuality_of_subsingleton : IsDuality ι 1 M := by
  refine ⟨fun {r s} h _ => ?_, fun h _ => ?_⟩
  · have := subsingleton_cohomology_of_subsingleton M
    have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
    have : Subsingleton (compactCohomology ι (dual 1 M) s →+ ZMod 1) :=
      ⟨fun f g => AddMonoidHom.ext fun _ => Subsingleton.elim _ _⟩
    exact bijective_of_subsingleton _
  · have := subsingleton_tateCompactCohomologyRes (localFamily ι S) (realFamily ι S) M
    have := subsingleton_cohomology_of_subsingleton (dual 1 M)
    exact bijective_of_subsingleton _

/-- For `M = 0` the nine-term sequence is exact for trivial reasons. -/
theorem isNineTermExact_of_subsingleton : IsNineTermExact ι 1 M := by
  have hM := subsingleton_cohomology_of_subsingleton M
  have hM' := subsingleton_cohomology_of_subsingleton (dual 1 M)
  have hP : ∀ n, Subsingleton (LocalTerm ι M n) := fun n => by
    have : ∀ v : S, Subsingleton (cohomology (localModule ι M v.1) n) := fun v =>
      subsingleton_cohomology_of_subsingleton _ n
    have : ∀ w : {w : InfinitePlace K // w.IsReal},
        Subsingleton (cohomology (realLocalModule ι M w.1) n) := fun w =>
      subsingleton_cohomology_of_subsingleton _ n
    exact inferInstanceAs (Subsingleton ((∀ v : S, cohomology (localModule ι M v.1) n) ×
      (∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι M w.1) n)))
  have hP0 : Subsingleton (LocalTermHat ι M) := by
    have := hP 0
    exact ⟨fun a b => by
      obtain ⟨a, rfl⟩ := hatMk_surjective ι M a
      obtain ⟨b, rfl⟩ := hatMk_surjective ι M b
      rw [Subsingleton.elim a b]⟩
  have hd : ∀ s, Subsingleton (cohomology (dual 1 M) s →+ QZ) := fun s =>
    ⟨fun f g => AddMonoidHom.ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]⟩
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, exact_of_subsingleton _ _, exact_of_subsingleton _ _,
    exact_of_subsingleton _ _, exact_of_subsingleton _ _, exact_of_subsingleton _ _,
    exact_of_subsingleton _ _, exact_of_subsingleton _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- For `M = 0` the Tate–Shafarevich groups are trivial. -/
theorem isShaDuality_of_subsingleton : IsShaDuality ι 1 M := by
  have hM := subsingleton_cohomology_of_subsingleton M 1
  have hM' := subsingleton_cohomology_of_subsingleton (dual 1 M) 2
  have h1 : Subsingleton (sha ι M 1) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have h2 : Subsingleton (sha ι (dual 1 M) 2) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have h3 : Subsingleton (sha ι (dual 1 M) 2 →+ QZ) :=
    ⟨fun f g => AddMonoidHom.ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]⟩
  have h4 : Subsingleton (sha ι M 1 →+ QZ) :=
    ⟨fun f g => AddMonoidHom.ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]⟩
  exact ⟨Finite.of_subsingleton, Finite.of_subsingleton, bijective_of_subsingleton _,
    bijective_of_subsingleton _⟩

end Trivial

section FromHypotheses

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- Duality for `M` from the abstract hypotheses. -/
theorem isDuality_of_hypotheses
    (P : letI : Fintype S := Fintype.ofFinite S
      TatePoitouTateHypotheses (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N)
        (trace ι S N) (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w.1))
    (hM : ∀ m : M, N • m = 0) : IsDuality ι N M := by
  let _ : Fintype S := Fintype.ofFinite S
  exact ⟨fun h hs => P.duality M hM h hs, fun h hr => P.bijective_ptTCompactDualMap M hM h hr⟩

/-- The nine-term sequence for `M` from the abstract hypotheses. -/
theorem isNineTermExact_of_hypotheses
    (P : letI : Fintype S := Fintype.ofFinite S
      TatePoitouTateHypotheses (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N)
        (trace ι S N) (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w.1))
    (hM : ∀ m : M, N • m = 0) : IsNineTermExact ι N M := by
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := P.isTateNineTermExact M hM
  exact ⟨a, b, c, d, e, f, g, h, i⟩

/-- The duality of the Tate–Shafarevich groups for `M` from the abstract hypotheses. -/
theorem isShaDuality_of_hypotheses
    (P : letI : Fintype S := Fintype.ofFinite S
      TatePoitouTateHypotheses (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N)
        (trace ι S N) (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w.1))
    (hM : ∀ m : M, N • m = 0) : IsShaDuality ι N M := by
  let _ : Fintype S := Fintype.ofFinite S
  have e1 := sha_eq_ptTSha ι M 1
  have e2 := sha_eq_ptTSha ι (dual N M) 2
  have hf1 := P.finite_ptTSha_one M hM
  have hf2 := P.finite_ptTSha_two M hM
  have hb := P.bijective_ptTShaPairing M hM
  have hbf := P.bijective_ptTShaPairing_flip M hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact hf1
  · rw [e2]; exact hf2
  · change Function.Bijective (((ptTShaPairing (localFamily ι S) (realFamily ι S)
      (dualizingModule K Ω S N) M (trace ι S N)).comp (AddSubgroup.inclusion e1.le)).compl₂
        (AddSubgroup.inclusion e2.le))
    rw [inclusion_eq_addSubgroupCongr e1, inclusion_eq_addSubgroupCongr e2]
    exact bijective_comp_compl₂ _ _ _ hb
  · change Function.Bijective (((ptTShaPairing (localFamily ι S) (realFamily ι S)
      (dualizingModule K Ω S N) M (trace ι S N)).comp (AddSubgroup.inclusion e1.le)).compl₂
        (AddSubgroup.inclusion e2.le)).flip
    rw [inclusion_eq_addSubgroupCongr e1, inclusion_eq_addSubgroupCongr e2]
    exact bijective_comp_compl₂_flip _ _ _ hbf

end FromHypotheses

end

end Langlands.GaloisCohomology.PoitouTate
