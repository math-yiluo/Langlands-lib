# Galois translates and inner conjugates of subgroups

Helper lemmas (internal; no literature counterpart beyond the standard fact that Galois
descent transport commutes with inner automorphisms up to the Galois conjugate point).

- `descent_comp_innerIso`, `descent_comp_innerIso_of_eq`: for abstract base maps
  `b : S' → S`, `a : S' → S'` with `a ≫ b = b`, the descent transport
  (`(GroupScheme.baseChange a).map _ ≫ (descentBaseChangeIso b a ha H).hom`) of a subgroup
  `f` followed by conjugation by `n` equals the transport of `f` followed by conjugation by the
  transported point. Proof: `Functor.map_comp`, `baseChange_innerIso_hom`, `innerIso_hom_comp`.
- `radicalGaloisHom_comp_innerIso`: for `K/k` and `σ ∈ Aut(K/k)`, the canonical Galois translate
  `radicalGaloisHom (f ≫ int(n)) σ` equals `radicalGaloisHom f σ ≫ int(σ n)`, where
  `σ n = rationalConjugate k K G σ n`. Proof: the previous lemma with
  `rationalConjugate_eq_baseChange_descent`.
- `range_comp_innerIso_of_mem`: conjugating a subgroup `j : H → G` by a point of `H` itself does
  not change its range (`innerIso_hom_comp`, `SubgroupFunctor.range_iso_comp`).
- `range_eq_of_innerIso_transport`: if `X = Y ≫ int(c)`, `range Y = range (P ≫ int(m))` and
  `c * m = q * pt` with `pt` a point of `P`, then `range X = range (P ≫ int(q))`. Proof:
  `SubgroupFunctor.range_comp_iso_eq_iff`, `innerIso_mul_hom` and the previous lemma.
