# Poitou–Tate for `G_S` from the abstract hypotheses

`Langlands/GaloisCohomology/Global/PoitouTate/Assembly.lean`, namespace `Langlands.GaloisCohomology.PoitouTate`.

Given the hypotheses `TatePoitouTateHypotheses` of the abstract nine-term sequence for `G_S`
(`tatePoitouTateHypotheses_of`), the three conclusions of Poitou–Tate duality for a finite module `M`
killed by `N` follow from the abstract theorems: `isDuality_of_hypotheses`,
`isNineTermExact_of_hypotheses`, `isShaDuality_of_hypotheses`. For `N = 1` the module is zero and
everything holds for trivial reasons (`isDuality_of_subsingleton`, `isNineTermExact_of_subsingleton`,
`isShaDuality_of_subsingleton`).

## Complete types

As printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.PoitouTate.bijective_comp_compl₂.{u_1, u_2, u_3, u_4, u_5} {A : Type u_1} {A' : Type u_2}
  {B : Type u_3} {B' : Type u_4} {C : Type u_5} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
  [AddCommGroup C] (f : A →+ B →+ C) (e : A' ≃+ A) (e' : B' ≃+ B) (hf : Function.Bijective ⇑f) :
  Function.Bijective ⇑((f.comp e.toAddMonoidHom).compl₂ e'.toAddMonoidHom)
Langlands.GaloisCohomology.PoitouTate.bijective_comp_compl₂_flip.{u_1, u_2, u_3, u_4, u_5} {A : Type u_1}
  {A' : Type u_2} {B : Type u_3} {B' : Type u_4} {C : Type u_5} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
  [AddCommGroup B'] [AddCommGroup C] (f : A →+ B →+ C) (e : A' ≃+ A) (e' : B' ≃+ B) (hf : Function.Bijective ⇑f.flip) :
  Function.Bijective ⇑((f.comp e.toAddMonoidHom).compl₂ e'.toAddMonoidHom).flip
Langlands.GaloisCohomology.PoitouTate.bijective_of_subsingleton.{u_1, u_2} {A : Type u_1} {B : Type u_2}
  [AddZeroClass A] [AddZeroClass B] [Subsingleton A] [Subsingleton B] (f : A →+ B) : Function.Bijective ⇑f
Langlands.GaloisCohomology.PoitouTate.exact_of_subsingleton.{u_1, u_2, u_3} {A : Type u_1} {B : Type u_2} {C : Type u_3}
  [AddGroup A] [AddGroup B] [AddGroup C] [Subsingleton B] (f : A →+ B) (g : B →+ C) : Function.Exact ⇑f ⇑g
Langlands.GaloisCohomology.PoitouTate.inclusion_eq_addSubgroupCongr.{u_1} {G : Type u_1} [AddGroup G]
  {H H' : AddSubgroup G} (h : H = H') : AddSubgroup.inclusion ⋯ = (AddEquiv.addSubgroupCongr h).toAddMonoidHom
Langlands.GaloisCohomology.PoitouTate.isDuality_of_hypotheses.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (P :
    Langlands.GaloisCohomology.TatePoitouTateHypotheses (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
      (Langlands.GaloisCohomology.PoitouTate.trace ι S N)
      (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) fun w =>
      Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w)
  (hM : ∀ (m : ↑M), N • m = 0) : Langlands.GaloisCohomology.PoitouTate.IsDuality ι N M
Langlands.GaloisCohomology.PoitouTate.isDuality_of_subsingleton.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Subsingleton ↑M] : Langlands.GaloisCohomology.PoitouTate.IsDuality ι 1 M
Langlands.GaloisCohomology.PoitouTate.isNineTermExact_of_hypotheses.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (P :
    Langlands.GaloisCohomology.TatePoitouTateHypotheses (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
      (Langlands.GaloisCohomology.PoitouTate.trace ι S N)
      (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) fun w =>
      Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w)
  (hM : ∀ (m : ↑M), N • m = 0) : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι N M
Langlands.GaloisCohomology.PoitouTate.isNineTermExact_of_subsingleton.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Subsingleton ↑M] : Langlands.GaloisCohomology.PoitouTate.IsNineTermExact ι 1 M
Langlands.GaloisCohomology.PoitouTate.isShaDuality_of_hypotheses.{u} {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
  [Algebra K Ω] [IsSepClosure K Ω] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [Finite ↑S] (ι : Langlands.Galois.PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M]
  (P :
    Langlands.GaloisCohomology.TatePoitouTateHypotheses (Langlands.GaloisCohomology.PoitouTate.localFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.realFamily ι S)
      (Langlands.GaloisCohomology.PoitouTate.dualizingModule K Ω S N)
      (Langlands.GaloisCohomology.PoitouTate.trace ι S N)
      (fun v => Langlands.GaloisCohomology.PoitouTate.invariantAt ι S N ↑v) fun w =>
      Langlands.GaloisCohomology.PoitouTate.realInvariantAt ι S N ↑w)
  (hM : ∀ (m : ↑M), N • m = 0) : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι N M
Langlands.GaloisCohomology.PoitouTate.isShaDuality_of_subsingleton.{u} {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} [Finite ↑S]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Langlands.IsSmoothRep M]
  [Finite ↑M] [Subsingleton ↑M] : Langlands.GaloisCohomology.PoitouTate.IsShaDuality ι 1 M
Langlands.GaloisCohomology.PoitouTate.subsingleton_dual_one.{u} {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) (Langlands.Galois.GaloisGroupUnramifiedOutside K Ω S)) [Subsingleton ↑M] :
  Subsingleton ↑(Langlands.GaloisCohomology.PoitouTate.dual 1 M)
Langlands.GaloisCohomology.PoitouTate.subsingleton_res.{u} {k G : Type u} [CommRing k] [Group G] {H : Type u} [Group H]
  (φ : H →* G) (A : Rep.{u, u, u} k G) [Subsingleton ↑A] : Subsingleton ↑(Rep.res φ A)
Langlands.GaloisCohomology.PoitouTate.subsingleton_tateCompactCohomologyRes.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {Hv : ι → Type u} [(v : ι) → Group (Hv v)]
  [(v : ι) → TopologicalSpace (Hv v)] [∀ (v : ι), IsTopologicalGroup (Hv v)] (φ : (v : ι) → Hv v →ₜ* G) {κ : Type u}
  {F : κ → Type u} [(w : κ) → Group (F w)] [(w : κ) → TopologicalSpace (F w)] [∀ (w : κ), IsTopologicalGroup (F w)]
  [(w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G) (A : Rep.{u, u, u} k G) [Langlands.IsSmoothRep A]
  [Subsingleton ↑A] (n : ℕ) : Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ A n)
```

## Outline of the proofs

The structures `IsDuality`, `IsNineTermExact`, `IsShaDuality` are read off the abstract layer's conclusions (`isTateNineTermExact`, `bijective_ptTShaPairing`, …); for `N = 1` every group is `0`.

## Declarations

`bijective_of_subsingleton`, `exact_of_subsingleton`, `subsingleton_res`, `subsingleton_tateCompactCohomologyRes`, `bijective_comp_compl₂`, `bijective_comp_compl₂_flip`, `inclusion_eq_addSubgroupCongr`, `subsingleton_dual_one`, `isDuality_of_subsingleton`, `isNineTermExact_of_subsingleton`, `isShaDuality_of_subsingleton`, `isDuality_of_hypotheses`, `isNineTermExact_of_hypotheses`, `isShaDuality_of_hypotheses`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008, corrected printing 2013), chapter VIII, §6: Theorem (8.6.7) (Poitou–Tate duality), p. 485; Proposition (8.6.8) (the pairing through cup products), p. 487; (8.6.10) (the long exact sequence of Poitou–Tate, and the real places in degrees `≥ 3`), pp. 489–490.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57; chapter II, §2, pp. 165–166 (cohomology with compact support).
