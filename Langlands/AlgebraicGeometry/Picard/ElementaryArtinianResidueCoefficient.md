# Functorial residue-fibre coefficient maps

Worker 219 defines the actual residue-fibre projection and its pushforward
structure module on each original scheme over `Spec R`. The coefficient map
for a morphism of schemes is the pushforward of its residue-fibre structure
map, followed by pushforward composition, equality transport across the
commuting square, and inverse pushforward composition.

This is internal sheaf-level infrastructure for the elementary ideal
cohomology comparison. The definitions retain the actual pullback functor and
pushforward functors. The projection naturality lemma follows directly from
the categorical pullback projection equation. This module imposes no
flatness, properness or Artinian condition; only the target local-ring
structure needed to form its residue field is used.
