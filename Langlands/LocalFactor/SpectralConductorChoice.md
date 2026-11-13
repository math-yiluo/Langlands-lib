# Finite Galois subfields presenting finitely many characters

Worker 4803 wrote this supporting module of
`SpectralConductor.spectralConductorRankOneReduction`.

## Results

- `exists_finiteGalois_of_isOpen`: every open neighbourhood `S` of `1` in Weil inertia
  contains the kernel of `weilInertiaRestriction F E` for some actual finite Galois
  subfield `E`. The proof is the argument of the Library's
  `HerbrandBridge.continuousWeilFiniteInertiaPresentation`. Transport `S` to absolute
  inertia by `localInertiaEquiv`, take a Krull neighbourhood
  (`krullTopology_mem_nhds_one_iff_of_normal`), and package its fixed field as a finite
  Galois subfield.
- `galoisClosure F L` is the normal closure of an intermediate field `L`, as a finite
  Galois subfield (`le_galoisClosure`).
- `exists_isPresentedAt`: a continuous character `χ` of `W_L` is presented at every
  finite Galois subfield containing a suitable `E`. Proof: the set of `w ∈ W_L` with
  `‖χ(w) - 1‖ < 1/2` is open in `W_L`, hence in `W_F` (`W_L` is open), and its trace on
  Weil inertia is open. Take `E` from the previous result. If `s ∈ W_L ∩ I_F` acts
  trivially on `M ⊇ E`, then every power `s^n` acts trivially on `E`, so
  `‖χ(s)^n - 1‖ < 1/2` for all `n`. The Library's no-small-subgroups lemma
  `complex_eq_one_of_forall_norm_pow_sub_one_lt` gives `χ(s) = 1`.
- `restrictionM_eq_one_of_le` and `IsPresentedAt.mono`: presentation passes to larger
  finite Galois subfields.
- `exists_presentingField`: for finitely many generators `Ind_L(χ - χ')` and any finite
  Galois `M₀`, some finite Galois `M ⊇ M₀` contains every inducing field and presents
  every character. Proof by induction on the finite set, taking the join of `M₀`, the
  Galois closures and the fields from `exists_isPresentedAt`.
